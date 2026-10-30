From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P013_1744C_traffic_light_lib.
Local Open Scope sac.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function solver -----*)

Definition solver_safety_wit_1_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (n_pre = (Zlength (lights)))) (PreH2 : (1 <= (Zlength (lights)))) (PreH3 : ((Zlength (lights)) <= 200000)) (PreH4 : (c_pre = 114)) (PreH5 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH6 : (Pre c_pre lights )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (103 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 103) ”
.

Definition solver_safety_wit_2_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (n_pre = (Zlength (lights)))) (PreH2 : (1 <= (Zlength (lights)))) (PreH3 : ((Zlength (lights)) <= 200000)) (PreH4 : (c_pre = 121)) (PreH5 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH6 : (Pre c_pre lights )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (103 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 103) ”
.

Definition solver_safety_wit_3_green :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (n_pre = (Zlength (lights)))) (PreH2 : (1 <= (Zlength (lights)))) (PreH3 : ((Zlength (lights)) <= 200000)) (PreH4 : (c_pre = 103)) (PreH5 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH6 : (Pre c_pre lights )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (103 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 103) ”
.

Definition solver_safety_wit_4_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre = 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ False ”
.

Definition solver_safety_wit_5_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre = 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ False ”
.

Definition solver_safety_wit_6_green :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 103)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ False ”
.

Definition solver_safety_wit_7_green :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre = 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 103)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  ((( &( "next_green" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_9_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  ((( &( "next_green" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  ((( &( "next_green" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_11_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  ((( &( "next_green" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_12_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_13_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "next_green" ) )) # Int  |-> (-1))
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (((2 * n_pre ) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((2 * n_pre ) - 1 )) ”
.

Definition solver_safety_wit_15_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "next_green" ) )) # Int  |-> (-1))
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((2 * n_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (2 * n_pre )) ”
.

Definition solver_safety_wit_16_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "next_green" ) )) # Int  |-> (-1))
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_17_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "next_green" ) )) # Int  |-> (-1))
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_18_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "next_green" ) )) # Int  |-> (-1))
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (((2 * n_pre ) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((2 * n_pre ) - 1 )) ”
.

Definition solver_safety_wit_19_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "next_green" ) )) # Int  |-> (-1))
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((2 * n_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (2 * n_pre )) ”
.

Definition solver_safety_wit_20_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "next_green" ) )) # Int  |-> (-1))
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_21_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "next_green" ) )) # Int  |-> (-1))
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_22_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (n = (Zlength (lights)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 200000)) (PreH4 : (c = 114)) (PreH5 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH6 : (Pre c lights )) (PreH7 : ((-1) <= i)) (PreH8 : (i < (2 * n ))) (PreH9 : (0 <= ans)) (PreH10 : (ans <= n)) (PreH11 : ((-1) <= next_green)) (PreH12 : (next_green < (2 * n ))) (PreH13 : (TrafficScanState c lights i ans next_green )) (PreH14 : (c_pre <> 103)) (PreH15 : (n_pre = (Zlength (lights)))) (PreH16 : (1 <= (Zlength (lights)))) (PreH17 : ((Zlength (lights)) <= 200000)) (PreH18 : (c_pre = 114)) (PreH19 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH20 : (Pre c_pre lights )),
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_23_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (n = (Zlength (lights)))) (PreH2 : (1 <= n)) (PreH3 : (n <= 200000)) (PreH4 : (c = 121)) (PreH5 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH6 : (Pre c lights )) (PreH7 : ((-1) <= i)) (PreH8 : (i < (2 * n ))) (PreH9 : (0 <= ans)) (PreH10 : (ans <= n)) (PreH11 : ((-1) <= next_green)) (PreH12 : (next_green < (2 * n ))) (PreH13 : (TrafficScanState c lights i ans next_green )) (PreH14 : (c_pre <> 103)) (PreH15 : (n_pre = (Zlength (lights)))) (PreH16 : (1 <= (Zlength (lights)))) (PreH17 : ((Zlength (lights)) <= 200000)) (PreH18 : (c_pre = 121)) (PreH19 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH20 : (Pre c_pre lights )),
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_24_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (0 <= (i % ( n ) ))) (PreH2 : ((i % ( n ) ) < n)) (PreH3 : (next_green <= INT_MAX)) (PreH4 : (ans <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= 0)) (PreH8 : (n = (Zlength (lights)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 200000)) (PreH11 : (c = 114)) (PreH12 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH13 : (Pre c lights )) (PreH14 : ((-1) <= i)) (PreH15 : (i < (2 * n ))) (PreH16 : (0 <= ans)) (PreH17 : (ans <= n)) (PreH18 : ((-1) <= next_green)) (PreH19 : (next_green < (2 * n ))) (PreH20 : (TrafficScanState c lights i ans next_green )) (PreH21 : (c_pre <> 103)) (PreH22 : (n_pre = (Zlength (lights)))) (PreH23 : (1 <= (Zlength (lights)))) (PreH24 : ((Zlength (lights)) <= 200000)) (PreH25 : (c_pre = 114)) (PreH26 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH27 : (Pre c_pre lights )),
  ((( &( "ch" ) )) # Char  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i <> (INT_MIN)) \/ (n <> (-1))) ”
  &&  “ (n <> 0) ”
.

Definition solver_safety_wit_25_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (0 <= (i % ( n ) ))) (PreH2 : ((i % ( n ) ) < n)) (PreH3 : (next_green <= INT_MAX)) (PreH4 : (ans <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= 0)) (PreH8 : (n = (Zlength (lights)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 200000)) (PreH11 : (c = 121)) (PreH12 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH13 : (Pre c lights )) (PreH14 : ((-1) <= i)) (PreH15 : (i < (2 * n ))) (PreH16 : (0 <= ans)) (PreH17 : (ans <= n)) (PreH18 : ((-1) <= next_green)) (PreH19 : (next_green < (2 * n ))) (PreH20 : (TrafficScanState c lights i ans next_green )) (PreH21 : (c_pre <> 103)) (PreH22 : (n_pre = (Zlength (lights)))) (PreH23 : (1 <= (Zlength (lights)))) (PreH24 : ((Zlength (lights)) <= 200000)) (PreH25 : (c_pre = 121)) (PreH26 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH27 : (Pre c_pre lights )),
  ((( &( "ch" ) )) # Char  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i <> (INT_MIN)) \/ (n <> (-1))) ”
  &&  “ (n <> 0) ”
.

Definition solver_safety_wit_26_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (0 <= (i % ( n ) ))) (PreH2 : ((i % ( n ) ) < n)) (PreH3 : (next_green <= INT_MAX)) (PreH4 : (ans <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= 0)) (PreH8 : (n = (Zlength (lights)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 200000)) (PreH11 : (c = 114)) (PreH12 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH13 : (Pre c lights )) (PreH14 : ((-1) <= i)) (PreH15 : (i < (2 * n ))) (PreH16 : (0 <= ans)) (PreH17 : (ans <= n)) (PreH18 : ((-1) <= next_green)) (PreH19 : (next_green < (2 * n ))) (PreH20 : (TrafficScanState c lights i ans next_green )) (PreH21 : (c_pre <> 103)) (PreH22 : (n_pre = (Zlength (lights)))) (PreH23 : (1 <= (Zlength (lights)))) (PreH24 : ((Zlength (lights)) <= 200000)) (PreH25 : (c_pre = 114)) (PreH26 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH27 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "ch" ) )) # Char  |-> (Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (103 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 103) ”
.

Definition solver_safety_wit_27_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (0 <= (i % ( n ) ))) (PreH2 : ((i % ( n ) ) < n)) (PreH3 : (next_green <= INT_MAX)) (PreH4 : (ans <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= 0)) (PreH8 : (n = (Zlength (lights)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 200000)) (PreH11 : (c = 121)) (PreH12 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH13 : (Pre c lights )) (PreH14 : ((-1) <= i)) (PreH15 : (i < (2 * n ))) (PreH16 : (0 <= ans)) (PreH17 : (ans <= n)) (PreH18 : ((-1) <= next_green)) (PreH19 : (next_green < (2 * n ))) (PreH20 : (TrafficScanState c lights i ans next_green )) (PreH21 : (c_pre <> 103)) (PreH22 : (n_pre = (Zlength (lights)))) (PreH23 : (1 <= (Zlength (lights)))) (PreH24 : ((Zlength (lights)) <= 200000)) (PreH25 : (c_pre = 121)) (PreH26 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH27 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "ch" ) )) # Char  |-> (Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (103 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 103) ”
.

Definition solver_safety_wit_28_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "ch" ) )) # Char  |-> (Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ False ”
.

Definition solver_safety_wit_29_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "ch" ) )) # Char  |-> (Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ False ”
.

Definition solver_safety_wit_30_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "ch" ) )) # Char  |-> (Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((next_green - i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (next_green - i )) ”
.

Definition solver_safety_wit_31_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "ch" ) )) # Char  |-> (Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((next_green - i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (next_green - i )) ”
.

Definition solver_safety_wit_32_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) > ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "ch" ) )) # Char  |-> (Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((next_green - i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (next_green - i )) ”
.

Definition solver_safety_wit_33_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) > ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "ch" ) )) # Char  |-> (Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((next_green - i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (next_green - i )) ”
.

Definition solver_safety_wit_34_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) > ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> (next_green - i ))
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_35_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) > ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> (next_green - i ))
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_36_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_37_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_38_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_39_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_40_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = 103)) (PreH3 : (0 <= (i % ( n ) ))) (PreH4 : ((i % ( n ) ) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 114)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_41_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = 103)) (PreH3 : (0 <= (i % ( n ) ))) (PreH4 : ((i % ( n ) ) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 121)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_42_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH3 : (0 <= (i % ( n ) ))) (PreH4 : ((i % ( n ) ) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 114)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_43_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH3 : (0 <= (i % ( n ) ))) (PreH4 : ((i % ( n ) ) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 121)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_44_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) <= ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_45_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) <= ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_entail_wit_1_red :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (c_pre = 114) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  “ ((-1) <= ((2 * n_pre ) - 1 )) ”
  &&  “ (((2 * n_pre ) - 1 ) < (2 * n_pre )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((-1) <= (-1)) ”
  &&  “ ((-1) < (2 * n_pre )) ”
  &&  “ (TrafficScanState c_pre lights ((2 * n_pre ) - 1 ) 0 (-1) ) ”
  &&  “ (c_pre <> 103) ”
  &&  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= (Zlength (lights))) ”
  &&  “ ((Zlength (lights)) <= 200000) ”
  &&  “ (c_pre = 114) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  TT && emp 
|--
  “ (TrafficScanState 114 lights ((2 * n_pre ) - 1 ) 0 (-1) ) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  emp
).

Definition solver_entail_wit_1_red_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  (TrafficScanState 114 lights ((2 * n_pre ) - 1 ) 0 (-1) )
.

Definition solver_entail_wit_1_red_split_goal_2 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 114)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))
.

Definition solver_entail_wit_2_yellow :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (c_pre = 121) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  “ ((-1) <= ((2 * n_pre ) - 1 )) ”
  &&  “ (((2 * n_pre ) - 1 ) < (2 * n_pre )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((-1) <= (-1)) ”
  &&  “ ((-1) < (2 * n_pre )) ”
  &&  “ (TrafficScanState c_pre lights ((2 * n_pre ) - 1 ) 0 (-1) ) ”
  &&  “ (c_pre <> 103) ”
  &&  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= (Zlength (lights))) ”
  &&  “ ((Zlength (lights)) <= 200000) ”
  &&  “ (c_pre = 121) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  TT && emp 
|--
  “ (TrafficScanState 121 lights ((2 * n_pre ) - 1 ) 0 (-1) ) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  emp
).

Definition solver_entail_wit_2_yellow_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  (TrafficScanState 121 lights ((2 * n_pre ) - 1 ) 0 (-1) )
.

Definition solver_entail_wit_2_yellow_split_goal_2 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre <> 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 121)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))
.

Definition solver_entail_wit_3_red :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i >= 0)) (PreH2 : (n = (Zlength (lights)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 200000)) (PreH5 : (c = 114)) (PreH6 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH7 : (Pre c lights )) (PreH8 : ((-1) <= i)) (PreH9 : (i < (2 * n ))) (PreH10 : (0 <= ans)) (PreH11 : (ans <= n)) (PreH12 : ((-1) <= next_green)) (PreH13 : (next_green < (2 * n ))) (PreH14 : (TrafficScanState c lights i ans next_green )) (PreH15 : (c_pre <> 103)) (PreH16 : (n_pre = (Zlength (lights)))) (PreH17 : (1 <= (Zlength (lights)))) (PreH18 : ((Zlength (lights)) <= 200000)) (PreH19 : (c_pre = 114)) (PreH20 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH21 : (Pre c_pre lights )),
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (0 <= (i % ( n ) )) ”
  &&  “ ((i % ( n ) ) < n) ”
  &&  “ (next_green <= INT_MAX) ”
  &&  “ (ans <= INT_MAX) ”
  &&  “ (next_green >= INT_MIN) ”
  &&  “ (ans >= INT_MIN) ”
  &&  “ (i >= 0) ”
  &&  “ (n = (Zlength (lights))) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= 200000) ”
  &&  “ (c = 114) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  “ (Pre c lights ) ”
  &&  “ ((-1) <= i) ”
  &&  “ (i < (2 * n )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= n) ”
  &&  “ ((-1) <= next_green) ”
  &&  “ (next_green < (2 * n )) ”
  &&  “ (TrafficScanState c lights i ans next_green ) ”
  &&  “ (c_pre <> 103) ”
  &&  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= (Zlength (lights))) ”
  &&  “ ((Zlength (lights)) <= 200000) ”
  &&  “ (c_pre = 114) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (next_green <= INT_MAX)) (PreH2 : (ans <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 114)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  TT && emp 
|--
  “ ((i % ( n ) ) < n) ”
  &&  “ (0 <= (i % ( n ) )) ”
  &&  emp
).

Definition solver_entail_wit_3_red_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (next_green <= INT_MAX)) (PreH2 : (ans <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 114)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  ((i % ( n ) ) < n)
.

Definition solver_entail_wit_3_red_split_goal_2 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (next_green <= INT_MAX)) (PreH2 : (ans <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 114)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  (0 <= (i % ( n ) ))
.

Definition solver_entail_wit_4_yellow :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i >= 0)) (PreH2 : (n = (Zlength (lights)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 200000)) (PreH5 : (c = 121)) (PreH6 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH7 : (Pre c lights )) (PreH8 : ((-1) <= i)) (PreH9 : (i < (2 * n ))) (PreH10 : (0 <= ans)) (PreH11 : (ans <= n)) (PreH12 : ((-1) <= next_green)) (PreH13 : (next_green < (2 * n ))) (PreH14 : (TrafficScanState c lights i ans next_green )) (PreH15 : (c_pre <> 103)) (PreH16 : (n_pre = (Zlength (lights)))) (PreH17 : (1 <= (Zlength (lights)))) (PreH18 : ((Zlength (lights)) <= 200000)) (PreH19 : (c_pre = 121)) (PreH20 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH21 : (Pre c_pre lights )),
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (0 <= (i % ( n ) )) ”
  &&  “ ((i % ( n ) ) < n) ”
  &&  “ (next_green <= INT_MAX) ”
  &&  “ (ans <= INT_MAX) ”
  &&  “ (next_green >= INT_MIN) ”
  &&  “ (ans >= INT_MIN) ”
  &&  “ (i >= 0) ”
  &&  “ (n = (Zlength (lights))) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= 200000) ”
  &&  “ (c = 121) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  “ (Pre c lights ) ”
  &&  “ ((-1) <= i) ”
  &&  “ (i < (2 * n )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= n) ”
  &&  “ ((-1) <= next_green) ”
  &&  “ (next_green < (2 * n )) ”
  &&  “ (TrafficScanState c lights i ans next_green ) ”
  &&  “ (c_pre <> 103) ”
  &&  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= (Zlength (lights))) ”
  &&  “ ((Zlength (lights)) <= 200000) ”
  &&  “ (c_pre = 121) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "next_green" ) )) # Int  |-> next_green)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (next_green <= INT_MAX)) (PreH2 : (ans <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 121)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  TT && emp 
|--
  “ ((i % ( n ) ) < n) ”
  &&  “ (0 <= (i % ( n ) )) ”
  &&  emp
).

Definition solver_entail_wit_4_yellow_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (next_green <= INT_MAX)) (PreH2 : (ans <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 121)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  ((i % ( n ) ) < n)
.

Definition solver_entail_wit_4_yellow_split_goal_2 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (next_green <= INT_MAX)) (PreH2 : (ans <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 121)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  (0 <= (i % ( n ) ))
.

Definition solver_entail_wit_5_1_red :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) > ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (n = (Zlength (lights))) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= 200000) ”
  &&  “ (c = 114) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  “ (Pre c lights ) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < (2 * n )) ”
  &&  “ (0 <= (next_green - i )) ”
  &&  “ ((next_green - i ) <= n) ”
  &&  “ ((-1) <= next_green) ”
  &&  “ (next_green < (2 * n )) ”
  &&  “ (TrafficScanState c lights (i - 1 ) (next_green - i ) next_green ) ”
  &&  “ (c_pre <> 103) ”
  &&  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= (Zlength (lights))) ”
  &&  “ ((Zlength (lights)) <= 200000) ”
  &&  “ (c_pre = 114) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) > ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  TT && emp 
|--
  “ (TrafficScanState 114 lights (i - 1 ) (next_green - i ) next_green ) ”
  &&  “ ((next_green - i ) <= n) ”
  &&  emp
).

Definition solver_entail_wit_5_1_red_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) > ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  (TrafficScanState 114 lights (i - 1 ) (next_green - i ) next_green )
.

Definition solver_entail_wit_5_1_red_split_goal_2 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) > ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  ((next_green - i ) <= n)
.

Definition solver_entail_wit_5_2_red :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (n = (Zlength (lights))) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= 200000) ”
  &&  “ (c = 114) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  “ (Pre c lights ) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < (2 * n )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= n) ”
  &&  “ ((-1) <= next_green) ”
  &&  “ (next_green < (2 * n )) ”
  &&  “ (TrafficScanState c lights (i - 1 ) ans next_green ) ”
  &&  “ (c_pre <> 103) ”
  &&  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= (Zlength (lights))) ”
  &&  “ ((Zlength (lights)) <= 200000) ”
  &&  “ (c_pre = 114) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  TT && emp 
|--
  “ (TrafficScanState 114 lights (i - 1 ) ans next_green ) ”
  &&  emp
).

Definition solver_entail_wit_5_2_red_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  (TrafficScanState 114 lights (i - 1 ) ans next_green )
.

Definition solver_entail_wit_5_3_red :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (n = (Zlength (lights))) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= 200000) ”
  &&  “ (c = 114) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  “ (Pre c lights ) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < (2 * n )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= n) ”
  &&  “ ((-1) <= i) ”
  &&  “ (i < (2 * n )) ”
  &&  “ (TrafficScanState c lights (i - 1 ) ans i ) ”
  &&  “ (c_pre <> 103) ”
  &&  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= (Zlength (lights))) ”
  &&  “ ((Zlength (lights)) <= 200000) ”
  &&  “ (c_pre = 114) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  TT && emp 
|--
  “ (TrafficScanState 114 lights (i - 1 ) ans i ) ”
  &&  emp
).

Definition solver_entail_wit_5_3_red_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 114)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 114)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  (TrafficScanState 114 lights (i - 1 ) ans i )
.

Definition solver_entail_wit_5_4_red :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = 103)) (PreH3 : (0 <= (i % ( n ) ))) (PreH4 : ((i % ( n ) ) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 114)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (n = (Zlength (lights))) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= 200000) ”
  &&  “ (c = 114) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  “ (Pre c lights ) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < (2 * n )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= n) ”
  &&  “ ((-1) <= i) ”
  &&  “ (i < (2 * n )) ”
  &&  “ (TrafficScanState c lights (i - 1 ) ans i ) ”
  &&  “ (c_pre <> 103) ”
  &&  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= (Zlength (lights))) ”
  &&  “ ((Zlength (lights)) <= 200000) ”
  &&  “ (c_pre = 114) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = 103)) (PreH3 : (0 <= (i % ( n ) ))) (PreH4 : ((i % ( n ) ) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 114)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  TT && emp 
|--
  “ (TrafficScanState 114 lights (i - 1 ) ans i ) ”
  &&  emp
).

Definition solver_entail_wit_5_4_red_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = 103)) (PreH3 : (0 <= (i % ( n ) ))) (PreH4 : ((i % ( n ) ) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 114)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  (TrafficScanState 114 lights (i - 1 ) ans i )
.

Definition solver_entail_wit_5_5_red :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH3 : (0 <= (i % ( n ) ))) (PreH4 : ((i % ( n ) ) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 114)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (n = (Zlength (lights))) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= 200000) ”
  &&  “ (c = 114) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  “ (Pre c lights ) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < (2 * n )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= n) ”
  &&  “ ((-1) <= next_green) ”
  &&  “ (next_green < (2 * n )) ”
  &&  “ (TrafficScanState c lights (i - 1 ) ans next_green ) ”
  &&  “ (c_pre <> 103) ”
  &&  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= (Zlength (lights))) ”
  &&  “ ((Zlength (lights)) <= 200000) ”
  &&  “ (c_pre = 114) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH3 : (0 <= (i % ( n ) ))) (PreH4 : ((i % ( n ) ) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 114)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  TT && emp 
|--
  “ (TrafficScanState 114 lights (i - 1 ) ans next_green ) ”
  &&  emp
).

Definition solver_entail_wit_5_5_red_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH3 : (0 <= (i % ( n ) ))) (PreH4 : ((i % ( n ) ) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 114)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 114)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  (TrafficScanState 114 lights (i - 1 ) ans next_green )
.

Definition solver_entail_wit_5_6_red :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) <= ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (n = (Zlength (lights))) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= 200000) ”
  &&  “ (c = 114) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  “ (Pre c lights ) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < (2 * n )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= n) ”
  &&  “ ((-1) <= next_green) ”
  &&  “ (next_green < (2 * n )) ”
  &&  “ (TrafficScanState c lights (i - 1 ) ans next_green ) ”
  &&  “ (c_pre <> 103) ”
  &&  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= (Zlength (lights))) ”
  &&  “ ((Zlength (lights)) <= 200000) ”
  &&  “ (c_pre = 114) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) <= ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  TT && emp 
|--
  “ (TrafficScanState 114 lights (i - 1 ) ans next_green ) ”
  &&  emp
).

Definition solver_entail_wit_5_6_red_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) <= ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 114)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 114)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  (TrafficScanState 114 lights (i - 1 ) ans next_green )
.

Definition solver_entail_wit_6_1_yellow :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) > ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (n = (Zlength (lights))) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= 200000) ”
  &&  “ (c = 121) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  “ (Pre c lights ) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < (2 * n )) ”
  &&  “ (0 <= (next_green - i )) ”
  &&  “ ((next_green - i ) <= n) ”
  &&  “ ((-1) <= next_green) ”
  &&  “ (next_green < (2 * n )) ”
  &&  “ (TrafficScanState c lights (i - 1 ) (next_green - i ) next_green ) ”
  &&  “ (c_pre <> 103) ”
  &&  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= (Zlength (lights))) ”
  &&  “ ((Zlength (lights)) <= 200000) ”
  &&  “ (c_pre = 121) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) > ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  TT && emp 
|--
  “ (TrafficScanState 121 lights (i - 1 ) (next_green - i ) next_green ) ”
  &&  “ ((next_green - i ) <= n) ”
  &&  emp
).

Definition solver_entail_wit_6_1_yellow_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) > ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  (TrafficScanState 121 lights (i - 1 ) (next_green - i ) next_green )
.

Definition solver_entail_wit_6_1_yellow_split_goal_2 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) > ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  ((next_green - i ) <= n)
.

Definition solver_entail_wit_6_2_yellow :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (n = (Zlength (lights))) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= 200000) ”
  &&  “ (c = 121) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  “ (Pre c lights ) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < (2 * n )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= n) ”
  &&  “ ((-1) <= next_green) ”
  &&  “ (next_green < (2 * n )) ”
  &&  “ (TrafficScanState c lights (i - 1 ) ans next_green ) ”
  &&  “ (c_pre <> 103) ”
  &&  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= (Zlength (lights))) ”
  &&  “ ((Zlength (lights)) <= 200000) ”
  &&  “ (c_pre = 121) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  TT && emp 
|--
  “ (TrafficScanState 121 lights (i - 1 ) ans next_green ) ”
  &&  emp
).

Definition solver_entail_wit_6_2_yellow_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  (TrafficScanState 121 lights (i - 1 ) ans next_green )
.

Definition solver_entail_wit_6_3_yellow :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (n = (Zlength (lights))) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= 200000) ”
  &&  “ (c = 121) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  “ (Pre c lights ) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < (2 * n )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= n) ”
  &&  “ ((-1) <= i) ”
  &&  “ (i < (2 * n )) ”
  &&  “ (TrafficScanState c lights (i - 1 ) ans i ) ”
  &&  “ (c_pre <> 103) ”
  &&  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= (Zlength (lights))) ”
  &&  “ ((Zlength (lights)) <= 200000) ”
  &&  “ (c_pre = 121) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  TT && emp 
|--
  “ (TrafficScanState 121 lights (i - 1 ) ans i ) ”
  &&  emp
).

Definition solver_entail_wit_6_3_yellow_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> c)) (PreH2 : (i < n)) (PreH3 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = 103)) (PreH4 : (0 <= (i % ( n ) ))) (PreH5 : ((i % ( n ) ) < n)) (PreH6 : (next_green <= INT_MAX)) (PreH7 : (ans <= INT_MAX)) (PreH8 : (next_green >= INT_MIN)) (PreH9 : (ans >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (n = (Zlength (lights)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 200000)) (PreH14 : (c = 121)) (PreH15 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH16 : (Pre c lights )) (PreH17 : ((-1) <= i)) (PreH18 : (i < (2 * n ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= n)) (PreH21 : ((-1) <= next_green)) (PreH22 : (next_green < (2 * n ))) (PreH23 : (TrafficScanState c lights i ans next_green )) (PreH24 : (c_pre <> 103)) (PreH25 : (n_pre = (Zlength (lights)))) (PreH26 : (1 <= (Zlength (lights)))) (PreH27 : ((Zlength (lights)) <= 200000)) (PreH28 : (c_pre = 121)) (PreH29 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH30 : (Pre c_pre lights )),
  (TrafficScanState 121 lights (i - 1 ) ans i )
.

Definition solver_entail_wit_6_4_yellow :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = 103)) (PreH3 : (0 <= (i % ( n ) ))) (PreH4 : ((i % ( n ) ) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 121)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (n = (Zlength (lights))) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= 200000) ”
  &&  “ (c = 121) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  “ (Pre c lights ) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < (2 * n )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= n) ”
  &&  “ ((-1) <= i) ”
  &&  “ (i < (2 * n )) ”
  &&  “ (TrafficScanState c lights (i - 1 ) ans i ) ”
  &&  “ (c_pre <> 103) ”
  &&  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= (Zlength (lights))) ”
  &&  “ ((Zlength (lights)) <= 200000) ”
  &&  “ (c_pre = 121) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = 103)) (PreH3 : (0 <= (i % ( n ) ))) (PreH4 : ((i % ( n ) ) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 121)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  TT && emp 
|--
  “ (TrafficScanState 121 lights (i - 1 ) ans i ) ”
  &&  emp
).

Definition solver_entail_wit_6_4_yellow_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = 103)) (PreH3 : (0 <= (i % ( n ) ))) (PreH4 : ((i % ( n ) ) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 121)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  (TrafficScanState 121 lights (i - 1 ) ans i )
.

Definition solver_entail_wit_6_5_yellow :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH3 : (0 <= (i % ( n ) ))) (PreH4 : ((i % ( n ) ) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 121)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (n = (Zlength (lights))) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= 200000) ”
  &&  “ (c = 121) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  “ (Pre c lights ) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < (2 * n )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= n) ”
  &&  “ ((-1) <= next_green) ”
  &&  “ (next_green < (2 * n )) ”
  &&  “ (TrafficScanState c lights (i - 1 ) ans next_green ) ”
  &&  “ (c_pre <> 103) ”
  &&  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= (Zlength (lights))) ”
  &&  “ ((Zlength (lights)) <= 200000) ”
  &&  “ (c_pre = 121) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH3 : (0 <= (i % ( n ) ))) (PreH4 : ((i % ( n ) ) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 121)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  TT && emp 
|--
  “ (TrafficScanState 121 lights (i - 1 ) ans next_green ) ”
  &&  emp
).

Definition solver_entail_wit_6_5_yellow_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH3 : (0 <= (i % ( n ) ))) (PreH4 : ((i % ( n ) ) < n)) (PreH5 : (next_green <= INT_MAX)) (PreH6 : (ans <= INT_MAX)) (PreH7 : (next_green >= INT_MIN)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (n = (Zlength (lights)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 200000)) (PreH13 : (c = 121)) (PreH14 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH15 : (Pre c lights )) (PreH16 : ((-1) <= i)) (PreH17 : (i < (2 * n ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= n)) (PreH20 : ((-1) <= next_green)) (PreH21 : (next_green < (2 * n ))) (PreH22 : (TrafficScanState c lights i ans next_green )) (PreH23 : (c_pre <> 103)) (PreH24 : (n_pre = (Zlength (lights)))) (PreH25 : (1 <= (Zlength (lights)))) (PreH26 : ((Zlength (lights)) <= 200000)) (PreH27 : (c_pre = 121)) (PreH28 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH29 : (Pre c_pre lights )),
  (TrafficScanState 121 lights (i - 1 ) ans next_green )
.

Definition solver_entail_wit_6_6_yellow :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) <= ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (n = (Zlength (lights))) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= 200000) ”
  &&  “ (c = 121) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  “ (Pre c lights ) ”
  &&  “ ((-1) <= (i - 1 )) ”
  &&  “ ((i - 1 ) < (2 * n )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= n) ”
  &&  “ ((-1) <= next_green) ”
  &&  “ (next_green < (2 * n )) ”
  &&  “ (TrafficScanState c lights (i - 1 ) ans next_green ) ”
  &&  “ (c_pre <> 103) ”
  &&  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= (Zlength (lights))) ”
  &&  “ ((Zlength (lights)) <= 200000) ”
  &&  “ (c_pre = 121) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) <= ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  TT && emp 
|--
  “ (TrafficScanState 121 lights (i - 1 ) ans next_green ) ”
  &&  emp
).

Definition solver_entail_wit_6_6_yellow_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : ((next_green - i ) <= ans)) (PreH2 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) = c)) (PreH3 : (i < n)) (PreH4 : ((Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0) <> 103)) (PreH5 : (0 <= (i % ( n ) ))) (PreH6 : ((i % ( n ) ) < n)) (PreH7 : (next_green <= INT_MAX)) (PreH8 : (ans <= INT_MAX)) (PreH9 : (next_green >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (n = (Zlength (lights)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 200000)) (PreH15 : (c = 121)) (PreH16 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH17 : (Pre c lights )) (PreH18 : ((-1) <= i)) (PreH19 : (i < (2 * n ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= n)) (PreH22 : ((-1) <= next_green)) (PreH23 : (next_green < (2 * n ))) (PreH24 : (TrafficScanState c lights i ans next_green )) (PreH25 : (c_pre <> 103)) (PreH26 : (n_pre = (Zlength (lights)))) (PreH27 : (1 <= (Zlength (lights)))) (PreH28 : ((Zlength (lights)) <= 200000)) (PreH29 : (c_pre = 121)) (PreH30 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH31 : (Pre c_pre lights )),
  (TrafficScanState 121 lights (i - 1 ) ans next_green )
.

Definition solver_return_wit_1_red :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i < 0)) (PreH2 : (n = (Zlength (lights)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 200000)) (PreH5 : (c = 114)) (PreH6 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH7 : (Pre c lights )) (PreH8 : ((-1) <= i)) (PreH9 : (i < (2 * n ))) (PreH10 : (0 <= ans)) (PreH11 : (ans <= n)) (PreH12 : ((-1) <= next_green)) (PreH13 : (next_green < (2 * n ))) (PreH14 : (TrafficScanState c lights i ans next_green )) (PreH15 : (c_pre <> 103)) (PreH16 : (n_pre = (Zlength (lights)))) (PreH17 : (1 <= (Zlength (lights)))) (PreH18 : ((Zlength (lights)) <= 200000)) (PreH19 : (c_pre = 114)) (PreH20 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH21 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (Spec c_pre lights ans ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i < 0)) (PreH2 : (n = (Zlength (lights)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 200000)) (PreH5 : (c = 114)) (PreH6 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH7 : (Pre c lights )) (PreH8 : ((-1) <= i)) (PreH9 : (i < (2 * n ))) (PreH10 : (0 <= ans)) (PreH11 : (ans <= n)) (PreH12 : ((-1) <= next_green)) (PreH13 : (next_green < (2 * n ))) (PreH14 : (TrafficScanState c lights i ans next_green )) (PreH15 : (c_pre <> 103)) (PreH16 : (n_pre = (Zlength (lights)))) (PreH17 : (1 <= (Zlength (lights)))) (PreH18 : ((Zlength (lights)) <= 200000)) (PreH19 : (c_pre = 114)) (PreH20 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH21 : (Pre c_pre lights )),
  TT && emp 
|--
  “ (Spec 114 lights ans ) ”
  &&  emp
).

Definition solver_return_wit_1_red_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i < 0)) (PreH2 : (n = (Zlength (lights)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 200000)) (PreH5 : (c = 114)) (PreH6 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH7 : (Pre c lights )) (PreH8 : ((-1) <= i)) (PreH9 : (i < (2 * n ))) (PreH10 : (0 <= ans)) (PreH11 : (ans <= n)) (PreH12 : ((-1) <= next_green)) (PreH13 : (next_green < (2 * n ))) (PreH14 : (TrafficScanState c lights i ans next_green )) (PreH15 : (c_pre <> 103)) (PreH16 : (n_pre = (Zlength (lights)))) (PreH17 : (1 <= (Zlength (lights)))) (PreH18 : ((Zlength (lights)) <= 200000)) (PreH19 : (c_pre = 114)) (PreH20 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH21 : (Pre c_pre lights )),
  (Spec 114 lights ans )
.

Definition solver_return_wit_2_yellow :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i < 0)) (PreH2 : (n = (Zlength (lights)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 200000)) (PreH5 : (c = 121)) (PreH6 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH7 : (Pre c lights )) (PreH8 : ((-1) <= i)) (PreH9 : (i < (2 * n ))) (PreH10 : (0 <= ans)) (PreH11 : (ans <= n)) (PreH12 : ((-1) <= next_green)) (PreH13 : (next_green < (2 * n ))) (PreH14 : (TrafficScanState c lights i ans next_green )) (PreH15 : (c_pre <> 103)) (PreH16 : (n_pre = (Zlength (lights)))) (PreH17 : (1 <= (Zlength (lights)))) (PreH18 : ((Zlength (lights)) <= 200000)) (PreH19 : (c_pre = 121)) (PreH20 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH21 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (Spec c_pre lights ans ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i < 0)) (PreH2 : (n = (Zlength (lights)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 200000)) (PreH5 : (c = 121)) (PreH6 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH7 : (Pre c lights )) (PreH8 : ((-1) <= i)) (PreH9 : (i < (2 * n ))) (PreH10 : (0 <= ans)) (PreH11 : (ans <= n)) (PreH12 : ((-1) <= next_green)) (PreH13 : (next_green < (2 * n ))) (PreH14 : (TrafficScanState c lights i ans next_green )) (PreH15 : (c_pre <> 103)) (PreH16 : (n_pre = (Zlength (lights)))) (PreH17 : (1 <= (Zlength (lights)))) (PreH18 : ((Zlength (lights)) <= 200000)) (PreH19 : (c_pre = 121)) (PreH20 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH21 : (Pre c_pre lights )),
  TT && emp 
|--
  “ (Spec 121 lights ans ) ”
  &&  emp
).

Definition solver_return_wit_2_yellow_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (i < 0)) (PreH2 : (n = (Zlength (lights)))) (PreH3 : (1 <= n)) (PreH4 : (n <= 200000)) (PreH5 : (c = 121)) (PreH6 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH7 : (Pre c lights )) (PreH8 : ((-1) <= i)) (PreH9 : (i < (2 * n ))) (PreH10 : (0 <= ans)) (PreH11 : (ans <= n)) (PreH12 : ((-1) <= next_green)) (PreH13 : (next_green < (2 * n ))) (PreH14 : (TrafficScanState c lights i ans next_green )) (PreH15 : (c_pre <> 103)) (PreH16 : (n_pre = (Zlength (lights)))) (PreH17 : (1 <= (Zlength (lights)))) (PreH18 : ((Zlength (lights)) <= 200000)) (PreH19 : (c_pre = 121)) (PreH20 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH21 : (Pre c_pre lights )),
  (Spec 121 lights ans )
.

Definition solver_return_wit_3_green :=
(
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre = 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 103)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (Spec c_pre lights 0 ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre = 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 103)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  TT && emp 
|--
  “ (Spec 103 lights 0 ) ”
  &&  emp
).

Definition solver_return_wit_3_green_split_goal_1 :=
forall (lights: (@list Z)) (n_pre: Z) (c_pre: Z) (PreH1 : (c_pre = 103)) (PreH2 : (n_pre = (Zlength (lights)))) (PreH3 : (1 <= (Zlength (lights)))) (PreH4 : ((Zlength (lights)) <= 200000)) (PreH5 : (c_pre = 103)) (PreH6 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH7 : (Pre c_pre lights )),
  (Spec 103 lights 0 )
.

Definition solver_partial_solve_wit_1_red :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (0 <= (i % ( n ) ))) (PreH2 : ((i % ( n ) ) < n)) (PreH3 : (next_green <= INT_MAX)) (PreH4 : (ans <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= 0)) (PreH8 : (n = (Zlength (lights)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 200000)) (PreH11 : (c = 114)) (PreH12 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH13 : (Pre c lights )) (PreH14 : ((-1) <= i)) (PreH15 : (i < (2 * n ))) (PreH16 : (0 <= ans)) (PreH17 : (ans <= n)) (PreH18 : ((-1) <= next_green)) (PreH19 : (next_green < (2 * n ))) (PreH20 : (TrafficScanState c lights i ans next_green )) (PreH21 : (c_pre <> 103)) (PreH22 : (n_pre = (Zlength (lights)))) (PreH23 : (1 <= (Zlength (lights)))) (PreH24 : ((Zlength (lights)) <= 200000)) (PreH25 : (c_pre = 114)) (PreH26 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH27 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (0 <= (i % ( n ) )) ”
  &&  “ ((i % ( n ) ) < n) ”
  &&  “ (next_green <= INT_MAX) ”
  &&  “ (ans <= INT_MAX) ”
  &&  “ (next_green >= INT_MIN) ”
  &&  “ (ans >= INT_MIN) ”
  &&  “ (i >= 0) ”
  &&  “ (n = (Zlength (lights))) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= 200000) ”
  &&  “ (c = 114) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  “ (Pre c lights ) ”
  &&  “ ((-1) <= i) ”
  &&  “ (i < (2 * n )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= n) ”
  &&  “ ((-1) <= next_green) ”
  &&  “ (next_green < (2 * n )) ”
  &&  “ (TrafficScanState c lights i ans next_green ) ”
  &&  “ (c_pre <> 103) ”
  &&  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= (Zlength (lights))) ”
  &&  “ ((Zlength (lights)) <= 200000) ”
  &&  “ (c_pre = 114) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  (((s_pre + ((i % ( n ) ) * sizeof(CHAR)))) # Char  |-> (Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre (i % ( n ) ) 0 (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
.

Definition solver_partial_solve_wit_2_yellow :=
forall (lights: (@list Z)) (s_pre: Z) (n_pre: Z) (c_pre: Z) (next_green: Z) (ans: Z) (i: Z) (c: Z) (n: Z) (PreH1 : (0 <= (i % ( n ) ))) (PreH2 : ((i % ( n ) ) < n)) (PreH3 : (next_green <= INT_MAX)) (PreH4 : (ans <= INT_MAX)) (PreH5 : (next_green >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= 0)) (PreH8 : (n = (Zlength (lights)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 200000)) (PreH11 : (c = 121)) (PreH12 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103)))) (PreH13 : (Pre c lights )) (PreH14 : ((-1) <= i)) (PreH15 : (i < (2 * n ))) (PreH16 : (0 <= ans)) (PreH17 : (ans <= n)) (PreH18 : ((-1) <= next_green)) (PreH19 : (next_green < (2 * n ))) (PreH20 : (TrafficScanState c lights i ans next_green )) (PreH21 : (c_pre <> 103)) (PreH22 : (n_pre = (Zlength (lights)))) (PreH23 : (1 <= (Zlength (lights)))) (PreH24 : ((Zlength (lights)) <= 200000)) (PreH25 : (c_pre = 121)) (PreH26 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103)))) (PreH27 : (Pre c_pre lights )),
  (CharArray.full s_pre (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (0 <= (i % ( n ) )) ”
  &&  “ ((i % ( n ) ) < n) ”
  &&  “ (next_green <= INT_MAX) ”
  &&  “ (ans <= INT_MAX) ”
  &&  “ (next_green >= INT_MIN) ”
  &&  “ (ans >= INT_MIN) ”
  &&  “ (i >= 0) ”
  &&  “ (n = (Zlength (lights))) ”
  &&  “ (1 <= n) ”
  &&  “ (n <= 200000) ”
  &&  “ (c = 121) ”
  &&  “ forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < n)) -> ((((Znth idx_2 lights 0) = 114) \/ ((Znth idx_2 lights 0) = 121)) \/ ((Znth idx_2 lights 0) = 103))) ”
  &&  “ (Pre c lights ) ”
  &&  “ ((-1) <= i) ”
  &&  “ (i < (2 * n )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= n) ”
  &&  “ ((-1) <= next_green) ”
  &&  “ (next_green < (2 * n )) ”
  &&  “ (TrafficScanState c lights i ans next_green ) ”
  &&  “ (c_pre <> 103) ”
  &&  “ (n_pre = (Zlength (lights))) ”
  &&  “ (1 <= (Zlength (lights))) ”
  &&  “ ((Zlength (lights)) <= 200000) ”
  &&  “ (c_pre = 121) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (lights)))) -> ((((Znth idx lights 0) = 114) \/ ((Znth idx lights 0) = 121)) \/ ((Znth idx lights 0) = 103))) ”
  &&  “ (Pre c_pre lights ) ”
  &&  (((s_pre + ((i % ( n ) ) * sizeof(CHAR)))) # Char  |-> (Znth (i % ( n ) ) (app (lights) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre (i % ( n ) ) 0 (n_pre + 1 ) (app (lights) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
.

Module Type VC_Correct.

Include string_Strategy_Correct.

Axiom proof_of_solver_safety_wit_1_red : solver_safety_wit_1_red.
Axiom proof_of_solver_safety_wit_2_yellow : solver_safety_wit_2_yellow.
Axiom proof_of_solver_safety_wit_3_green : solver_safety_wit_3_green.
Axiom proof_of_solver_safety_wit_4_red : solver_safety_wit_4_red.
Axiom proof_of_solver_safety_wit_5_yellow : solver_safety_wit_5_yellow.
Axiom proof_of_solver_safety_wit_6_green : solver_safety_wit_6_green.
Axiom proof_of_solver_safety_wit_7_green : solver_safety_wit_7_green.
Axiom proof_of_solver_safety_wit_8_red : solver_safety_wit_8_red.
Axiom proof_of_solver_safety_wit_9_red : solver_safety_wit_9_red.
Axiom proof_of_solver_safety_wit_10_yellow : solver_safety_wit_10_yellow.
Axiom proof_of_solver_safety_wit_11_yellow : solver_safety_wit_11_yellow.
Axiom proof_of_solver_safety_wit_12_red : solver_safety_wit_12_red.
Axiom proof_of_solver_safety_wit_13_yellow : solver_safety_wit_13_yellow.
Axiom proof_of_solver_safety_wit_14_red : solver_safety_wit_14_red.
Axiom proof_of_solver_safety_wit_15_red : solver_safety_wit_15_red.
Axiom proof_of_solver_safety_wit_16_red : solver_safety_wit_16_red.
Axiom proof_of_solver_safety_wit_17_red : solver_safety_wit_17_red.
Axiom proof_of_solver_safety_wit_18_yellow : solver_safety_wit_18_yellow.
Axiom proof_of_solver_safety_wit_19_yellow : solver_safety_wit_19_yellow.
Axiom proof_of_solver_safety_wit_20_yellow : solver_safety_wit_20_yellow.
Axiom proof_of_solver_safety_wit_21_yellow : solver_safety_wit_21_yellow.
Axiom proof_of_solver_safety_wit_22_red : solver_safety_wit_22_red.
Axiom proof_of_solver_safety_wit_23_yellow : solver_safety_wit_23_yellow.
Axiom proof_of_solver_safety_wit_24_red : solver_safety_wit_24_red.
Axiom proof_of_solver_safety_wit_25_yellow : solver_safety_wit_25_yellow.
Axiom proof_of_solver_safety_wit_26_red : solver_safety_wit_26_red.
Axiom proof_of_solver_safety_wit_27_yellow : solver_safety_wit_27_yellow.
Axiom proof_of_solver_safety_wit_28_yellow : solver_safety_wit_28_yellow.
Axiom proof_of_solver_safety_wit_29_red : solver_safety_wit_29_red.
Axiom proof_of_solver_safety_wit_30_red : solver_safety_wit_30_red.
Axiom proof_of_solver_safety_wit_31_yellow : solver_safety_wit_31_yellow.
Axiom proof_of_solver_safety_wit_32_red : solver_safety_wit_32_red.
Axiom proof_of_solver_safety_wit_33_yellow : solver_safety_wit_33_yellow.
Axiom proof_of_solver_safety_wit_34_red : solver_safety_wit_34_red.
Axiom proof_of_solver_safety_wit_35_yellow : solver_safety_wit_35_yellow.
Axiom proof_of_solver_safety_wit_36_yellow : solver_safety_wit_36_yellow.
Axiom proof_of_solver_safety_wit_37_red : solver_safety_wit_37_red.
Axiom proof_of_solver_safety_wit_38_yellow : solver_safety_wit_38_yellow.
Axiom proof_of_solver_safety_wit_39_red : solver_safety_wit_39_red.
Axiom proof_of_solver_safety_wit_40_red : solver_safety_wit_40_red.
Axiom proof_of_solver_safety_wit_41_yellow : solver_safety_wit_41_yellow.
Axiom proof_of_solver_safety_wit_42_red : solver_safety_wit_42_red.
Axiom proof_of_solver_safety_wit_43_yellow : solver_safety_wit_43_yellow.
Axiom proof_of_solver_safety_wit_44_red : solver_safety_wit_44_red.
Axiom proof_of_solver_safety_wit_45_yellow : solver_safety_wit_45_yellow.
Axiom proof_of_solver_entail_wit_1_red : solver_entail_wit_1_red.
Axiom proof_of_solver_entail_wit_2_yellow : solver_entail_wit_2_yellow.
Axiom proof_of_solver_entail_wit_3_red : solver_entail_wit_3_red.
Axiom proof_of_solver_entail_wit_4_yellow : solver_entail_wit_4_yellow.
Axiom proof_of_solver_entail_wit_5_1_red : solver_entail_wit_5_1_red.
Axiom proof_of_solver_entail_wit_5_2_red : solver_entail_wit_5_2_red.
Axiom proof_of_solver_entail_wit_5_3_red : solver_entail_wit_5_3_red.
Axiom proof_of_solver_entail_wit_5_4_red : solver_entail_wit_5_4_red.
Axiom proof_of_solver_entail_wit_5_5_red : solver_entail_wit_5_5_red.
Axiom proof_of_solver_entail_wit_5_6_red : solver_entail_wit_5_6_red.
Axiom proof_of_solver_entail_wit_6_1_yellow : solver_entail_wit_6_1_yellow.
Axiom proof_of_solver_entail_wit_6_2_yellow : solver_entail_wit_6_2_yellow.
Axiom proof_of_solver_entail_wit_6_3_yellow : solver_entail_wit_6_3_yellow.
Axiom proof_of_solver_entail_wit_6_4_yellow : solver_entail_wit_6_4_yellow.
Axiom proof_of_solver_entail_wit_6_5_yellow : solver_entail_wit_6_5_yellow.
Axiom proof_of_solver_entail_wit_6_6_yellow : solver_entail_wit_6_6_yellow.
Axiom proof_of_solver_return_wit_1_red : solver_return_wit_1_red.
Axiom proof_of_solver_return_wit_2_yellow : solver_return_wit_2_yellow.
Axiom proof_of_solver_return_wit_3_green : solver_return_wit_3_green.
Axiom proof_of_solver_partial_solve_wit_1_red : solver_partial_solve_wit_1_red.
Axiom proof_of_solver_partial_solve_wit_2_yellow : solver_partial_solve_wit_2_yellow.

End VC_Correct.
