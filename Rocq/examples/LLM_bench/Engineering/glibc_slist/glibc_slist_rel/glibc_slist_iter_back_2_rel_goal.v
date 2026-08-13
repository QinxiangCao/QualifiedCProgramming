Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.MonadErr Require Export StateRelMonadErr.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
Require Import glibc_slist_lib.
Require Import glibc_slist_iter_back_2_rel_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.

(*----- Function glibc_slist_clean_iter_back_2 -----*)

Definition glibc_slist_clean_iter_back_2_safety_wit_1 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (range l1_low_level_spec )) (PreH2 : (safeExec ATrue (glibc_slist_clean_iter_back_2_M (l1_low_level_spec)) X_low_level_spec )) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "prev" ) )) # Ptr  |->_)
  **  ((( &( "stop" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sllseg x_pre 0 l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_iter_back_2_safety_wit_2 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (range l1_low_level_spec )) (PreH2 : (safeExec ATrue (glibc_slist_clean_iter_back_2_M (l1_low_level_spec)) X_low_level_spec )) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "prev" ) )) # Ptr  |->_)
  **  ((( &( "stop" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sllseg x_pre 0 l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_iter_back_2_safety_wit_3 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st: Z) (s: Z) (l1_1: (@list Z)) (ldone: (@list Z)) (PreH1 : (x_pre <> st)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop1 (l1_1) (s))) ((glibc_slist_clean_iter_back_2_M_loop1_end ((app (l1_1) (ldone)))))) X_low_level_spec )) (PreH3 : (range l1_1 )) (PreH4 : ((INT_MIN) <= s)) (PreH5 : (s <= INT_MAX)) (PreH6 : (range l1_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "prev" ) )) # Ptr  |->_)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "stop" ) )) # Ptr  |-> st)
  **  ((( &( "sum" ) )) # Int  |-> s)
  **  (sllseg x_pre st l1_1 )
  **  (sll st ldone )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_iter_back_2_safety_wit_4 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (p: Z) (st: Z) (s: Z) (lpre: (@list Z)) (ldone: (@list Z)) (y: Z) (v: Z) (node: Z) (PreH1 : (y = st)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 ((cons (v) ((@nil Z)))) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre) ((cons (v) ((@nil Z)))))) (ldone))) ((app (lpre) ((cons (v) ((@nil Z)))))) (s)))) X_low_level_spec )) (PreH3 : (node <> 0)) (PreH4 : (range lpre )) (PreH5 : (range (cons (v) ((@nil Z))) )) (PreH6 : (range (app (lpre) ((cons (v) ((@nil Z))))) )) (PreH7 : (range l1_low_level_spec )) (PreH8 : ((INT_MIN) <= s)) (PreH9 : (s <= INT_MAX)) (PreH10 : ((INT_MIN) <= (s + v ))) (PreH11 : ((s + v ) <= INT_MAX)) (PreH12 : (glibc_slist_clean_iter_back_2_prev_case p lpre node x_pre )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((( &( "prev" ) )) # Ptr  |-> p)
  **  ((( &( "stop" ) )) # Ptr  |-> st)
  **  ((( &( "sum" ) )) # Int  |-> s)
  **  (sllseg x_pre node lpre )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sll y ldone )
|--
  “ ((s + v ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (s + v )) ”
.

Definition glibc_slist_clean_iter_back_2_safety_wit_5 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (p: Z) (st: Z) (s: Z) (lpre: (@list Z)) (ldone: (@list Z)) (y: Z) (v: Z) (node: Z) (PreH1 : (y = st)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 ((cons (v) ((@nil Z)))) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre) ((cons (v) ((@nil Z)))))) (ldone))) ((app (lpre) ((cons (v) ((@nil Z)))))) (s)))) X_low_level_spec )) (PreH3 : (node <> 0)) (PreH4 : (range lpre )) (PreH5 : (range (cons (v) ((@nil Z))) )) (PreH6 : (range (app (lpre) ((cons (v) ((@nil Z))))) )) (PreH7 : (range l1_low_level_spec )) (PreH8 : ((INT_MIN) <= s)) (PreH9 : (s <= INT_MAX)) (PreH10 : ((INT_MIN) <= (s + v ))) (PreH11 : ((s + v ) <= INT_MAX)) (PreH12 : (glibc_slist_clean_iter_back_2_prev_case p lpre node x_pre )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((( &( "prev" ) )) # Ptr  |-> p)
  **  ((( &( "stop" ) )) # Ptr  |-> node)
  **  ((( &( "sum" ) )) # Int  |-> (s + v ))
  **  (sllseg x_pre node lpre )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sll y ldone )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_iter_back_2_entail_wit_1 := 
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (range l1_low_level_spec )) (PreH2 : (safeExec ATrue (glibc_slist_clean_iter_back_2_M (l1_low_level_spec)) X_low_level_spec )) ,
  (sllseg x_pre 0 l1_low_level_spec )
|--
  EX (l1_1: (@list Z))  (ldone: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop1 (l1_1) (0))) ((glibc_slist_clean_iter_back_2_M_loop1_end ((app (l1_1) (ldone)))))) X_low_level_spec ) ” 
  &&  “ (range l1_1 ) ” 
  &&  “ ((INT_MIN) <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (range l1_low_level_spec ) ”
  &&  (sllseg x_pre 0 l1_1 )
  **  (sll 0 ldone )
) \/
(
forall (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (range l1_low_level_spec )) (PreH2 : (safeExec ATrue (glibc_slist_clean_iter_back_2_M (l1_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop1 (l1_low_level_spec) (0))) ((glibc_slist_clean_iter_back_2_M_loop1_end ((app (l1_low_level_spec) ((@nil Z))))))) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_iter_back_2_entail_wit_1_split_goal_1 := 
forall (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (range l1_low_level_spec )) (PreH2 : (safeExec ATrue (glibc_slist_clean_iter_back_2_M (l1_low_level_spec)) X_low_level_spec )) ,
  (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop1 (l1_low_level_spec) (0))) ((glibc_slist_clean_iter_back_2_M_loop1_end ((app (l1_low_level_spec) ((@nil Z))))))) X_low_level_spec )
.

Definition glibc_slist_clean_iter_back_2_entail_wit_2 := 
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st: Z) (s: Z) (l1_1: (@list Z)) (ldone_2: (@list Z)) (PreH1 : (x_pre <> st)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop1 (l1_1) (s))) ((glibc_slist_clean_iter_back_2_M_loop1_end ((app (l1_1) (ldone_2)))))) X_low_level_spec )) (PreH3 : (range l1_1 )) (PreH4 : ((INT_MIN) <= s)) (PreH5 : (s <= INT_MAX)) (PreH6 : (range l1_low_level_spec )) ,
  (sllseg x_pre st l1_1 )
  **  (sll st ldone_2 )
|--
  EX (y: Z)  (ldone: (@list Z))  (v: Z)  (lrest: (@list Z))  (l2_1: (@list Z)) ,
  “ (l2_1 = (cons (v) (lrest))) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 (l2_1) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app ((@nil Z)) (l2_1))) (ldone))) ((app ((@nil Z)) (l2_1))) (s)))) X_low_level_spec ) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> st) ” 
  &&  “ (range (@nil Z) ) ” 
  &&  “ (range l2_1 ) ” 
  &&  “ (range (app ((@nil Z)) (l2_1)) ) ” 
  &&  “ (range l1_low_level_spec ) ” 
  &&  “ ((INT_MIN) <= s) ” 
  &&  “ (s <= INT_MAX) ” 
  &&  “ (glibc_slist_clean_iter_back_2_prev_case 0 (@nil Z) x_pre x_pre ) ”
  &&  (sllseg x_pre x_pre (@nil Z) )
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sllseg y st lrest )
  **  (sll st ldone )
) \/
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st: Z) (s: Z) (l1_1: (@list Z)) (ldone_2: (@list Z)) (PreH1 : (x_pre <> st)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop1 (l1_1) (s))) ((glibc_slist_clean_iter_back_2_M_loop1_end ((app (l1_1) (ldone_2)))))) X_low_level_spec )) (PreH3 : (range l1_1 )) (PreH4 : ((INT_MIN) <= s)) (PreH5 : (s <= INT_MAX)) (PreH6 : (range l1_low_level_spec )) ,
  (sllseg x_pre st l1_1 )
|--
  EX (y: Z)  (v: Z)  (lrest: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 ((cons (v) (lrest))) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app ((@nil Z)) ((cons (v) (lrest))))) (ldone_2))) ((app ((@nil Z)) ((cons (v) (lrest))))) (s)))) X_low_level_spec ) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> st) ” 
  &&  “ (range (@nil Z) ) ” 
  &&  “ (range (cons (v) (lrest)) ) ” 
  &&  “ (range (app ((@nil Z)) ((cons (v) (lrest)))) ) ” 
  &&  “ (range l1_low_level_spec ) ” 
  &&  “ ((INT_MIN) <= s) ” 
  &&  “ (s <= INT_MAX) ” 
  &&  “ (glibc_slist_clean_iter_back_2_prev_case 0 (@nil Z) x_pre x_pre ) ”
  &&  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sllseg y st lrest )
).

Definition glibc_slist_clean_iter_back_2_entail_wit_3 := 
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st: Z) (s: Z) (l2_1: (@list Z)) (ldone_2: (@list Z)) (y_2: Z) (v: Z) (lrest: (@list Z)) (PreH1 : (l2_1 = (cons (v) (lrest)))) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 (l2_1) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app ((@nil Z)) (l2_1))) (ldone_2))) ((app ((@nil Z)) (l2_1))) (s)))) X_low_level_spec )) (PreH3 : (x_pre <> 0)) (PreH4 : (x_pre <> st)) (PreH5 : (range (@nil Z) )) (PreH6 : (range l2_1 )) (PreH7 : (range (app ((@nil Z)) (l2_1)) )) (PreH8 : (range l1_low_level_spec )) (PreH9 : ((INT_MIN) <= s)) (PreH10 : (s <= INT_MAX)) (PreH11 : (glibc_slist_clean_iter_back_2_prev_case 0 (@nil Z) x_pre x_pre )) ,
  (sllseg x_pre x_pre (@nil Z) )
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sllseg y_2 st lrest )
  **  (sll st ldone_2 )
|--
  EX (y: Z)  (ldone: (@list Z))  (lpre: (@list Z))  (v_2: Z)  (lrest_2: (@list Z))  (l2_1_2: (@list Z)) ,
  “ (l2_1_2 = (cons (v_2) (lrest_2))) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 (l2_1_2) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre) (l2_1_2))) (ldone))) ((app (lpre) (l2_1_2))) (s)))) X_low_level_spec ) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> st) ” 
  &&  “ (range lpre ) ” 
  &&  “ (range l2_1_2 ) ” 
  &&  “ (range (app (lpre) (l2_1_2)) ) ” 
  &&  “ (range l1_low_level_spec ) ” 
  &&  “ ((INT_MIN) <= s) ” 
  &&  “ (s <= INT_MAX) ” 
  &&  “ (glibc_slist_clean_iter_back_2_prev_case 0 lpre x_pre x_pre ) ” 
  &&  “ (l2_1 = (cons (v) (lrest))) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> st) ” 
  &&  “ (range (@nil Z) ) ” 
  &&  “ (range l2_1 ) ” 
  &&  “ (range (app ((@nil Z)) (l2_1)) ) ” 
  &&  “ (range l1_low_level_spec ) ” 
  &&  “ ((INT_MIN) <= s) ” 
  &&  “ (s <= INT_MAX) ” 
  &&  “ (glibc_slist_clean_iter_back_2_prev_case 0 (@nil Z) x_pre x_pre ) ”
  &&  (sllseg x_pre x_pre lpre )
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  (sllseg y st lrest_2 )
  **  (sll st ldone )
  **  (sllseg x_pre x_pre (@nil Z) )
) \/
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st: Z) (s: Z) (l2_1: (@list Z)) (ldone_2: (@list Z)) (v: Z) (lrest: (@list Z)) (PreH1 : (l2_1 = (cons (v) (lrest)))) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 (l2_1) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app ((@nil Z)) (l2_1))) (ldone_2))) ((app ((@nil Z)) (l2_1))) (s)))) X_low_level_spec )) (PreH3 : (x_pre <> 0)) (PreH4 : (x_pre <> st)) (PreH5 : (range (@nil Z) )) (PreH6 : (range l2_1 )) (PreH7 : (range (app ((@nil Z)) (l2_1)) )) (PreH8 : (range l1_low_level_spec )) (PreH9 : ((INT_MIN) <= s)) (PreH10 : (s <= INT_MAX)) (PreH11 : (glibc_slist_clean_iter_back_2_prev_case 0 (@nil Z) x_pre x_pre )) ,
  (sllseg x_pre x_pre (@nil Z) )
|--
  TT && emp 
).

Definition glibc_slist_clean_iter_back_2_entail_wit_3_split_goal_spatial := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st: Z) (s: Z) (l2_1: (@list Z)) (ldone_2: (@list Z)) (v: Z) (lrest: (@list Z)) (PreH1 : (l2_1 = (cons (v) (lrest)))) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 (l2_1) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app ((@nil Z)) (l2_1))) (ldone_2))) ((app ((@nil Z)) (l2_1))) (s)))) X_low_level_spec )) (PreH3 : (x_pre <> 0)) (PreH4 : (x_pre <> st)) (PreH5 : (range (@nil Z) )) (PreH6 : (range l2_1 )) (PreH7 : (range (app ((@nil Z)) (l2_1)) )) (PreH8 : (range l1_low_level_spec )) (PreH9 : ((INT_MIN) <= s)) (PreH10 : (s <= INT_MAX)) (PreH11 : (glibc_slist_clean_iter_back_2_prev_case 0 (@nil Z) x_pre x_pre )) ,
  (sllseg x_pre x_pre (@nil Z) )
|--
  TT && emp 
.

Definition glibc_slist_clean_iter_back_2_entail_wit_4 := 
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st: Z) (s: Z) (l2_1: (@list Z)) (v: Z) (lrest: (@list Z)) (y_2: Z) (p: Z) (st_2: Z) (node: Z) (ldone_2: (@list Z)) (lpre_2: (@list Z)) (s_2: Z) (v_3: Z) (lrest_3: (@list Z)) (l2_1_3: (@list Z)) (PreH1 : (y_2 <> st_2)) (PreH2 : (l2_1_3 = (cons (v_3) (lrest_3)))) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 (l2_1_3) (s_2))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre_2) (l2_1_3))) (ldone_2))) ((app (lpre_2) (l2_1_3))) (s_2)))) X_low_level_spec )) (PreH4 : (node <> 0)) (PreH5 : (x_pre <> st_2)) (PreH6 : (range lpre_2 )) (PreH7 : (range l2_1_3 )) (PreH8 : (range (app (lpre_2) (l2_1_3)) )) (PreH9 : (range l1_low_level_spec )) (PreH10 : ((INT_MIN) <= s_2)) (PreH11 : (s_2 <= INT_MAX)) (PreH12 : (glibc_slist_clean_iter_back_2_prev_case p lpre_2 node x_pre )) (PreH13 : (l2_1 = (cons (v) (lrest)))) (PreH14 : (x_pre <> 0)) (PreH15 : (x_pre <> st)) (PreH16 : (range (@nil Z) )) (PreH17 : (range l2_1 )) (PreH18 : (range (app ((@nil Z)) (l2_1)) )) (PreH19 : (range l1_low_level_spec )) (PreH20 : ((INT_MIN) <= s)) (PreH21 : (s <= INT_MAX)) (PreH22 : (glibc_slist_clean_iter_back_2_prev_case 0 (@nil Z) x_pre x_pre )) ,
  (sllseg x_pre node lpre_2 )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((node)  # "list" ->ₛ "data")) # Int  |-> v_3)
  **  (sllseg y_2 st_2 lrest_3 )
  **  (sll st_2 ldone_2 )
  **  (sllseg x_pre x_pre (@nil Z) )
|--
  EX (y: Z)  (ldone: (@list Z))  (lpre: (@list Z))  (v_2: Z)  (lrest_2: (@list Z))  (l2_1_2: (@list Z)) ,
  “ (l2_1_2 = (cons (v_2) (lrest_2))) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 (l2_1_2) (s_2))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre) (l2_1_2))) (ldone))) ((app (lpre) (l2_1_2))) (s_2)))) X_low_level_spec ) ” 
  &&  “ (y_2 <> 0) ” 
  &&  “ (x_pre <> st_2) ” 
  &&  “ (range lpre ) ” 
  &&  “ (range l2_1_2 ) ” 
  &&  “ (range (app (lpre) (l2_1_2)) ) ” 
  &&  “ (range l1_low_level_spec ) ” 
  &&  “ ((INT_MIN) <= s_2) ” 
  &&  “ (s_2 <= INT_MAX) ” 
  &&  “ (glibc_slist_clean_iter_back_2_prev_case node lpre y_2 x_pre ) ” 
  &&  “ (l2_1 = (cons (v) (lrest))) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> st) ” 
  &&  “ (range (@nil Z) ) ” 
  &&  “ (range l2_1 ) ” 
  &&  “ (range (app ((@nil Z)) (l2_1)) ) ” 
  &&  “ (range l1_low_level_spec ) ” 
  &&  “ ((INT_MIN) <= s) ” 
  &&  “ (s <= INT_MAX) ” 
  &&  “ (glibc_slist_clean_iter_back_2_prev_case 0 (@nil Z) x_pre x_pre ) ”
  &&  (sllseg x_pre y_2 lpre )
  **  ((&((y_2)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((y_2)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  (sllseg y st_2 lrest_2 )
  **  (sll st_2 ldone )
  **  (sllseg x_pre x_pre (@nil Z) )
) \/
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st: Z) (s: Z) (l2_1: (@list Z)) (v: Z) (lrest: (@list Z)) (y_2: Z) (p: Z) (st_2: Z) (node: Z) (ldone_2: (@list Z)) (lpre_2: (@list Z)) (s_2: Z) (v_3: Z) (lrest_3: (@list Z)) (l2_1_3: (@list Z)) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (v_3 >= INT_MIN)) (PreH3 : (y_2 <> st_2)) (PreH4 : (l2_1_3 = (cons (v_3) (lrest_3)))) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 (l2_1_3) (s_2))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre_2) (l2_1_3))) (ldone_2))) ((app (lpre_2) (l2_1_3))) (s_2)))) X_low_level_spec )) (PreH6 : (node <> 0)) (PreH7 : (x_pre <> st_2)) (PreH8 : (range lpre_2 )) (PreH9 : (range l2_1_3 )) (PreH10 : (range (app (lpre_2) (l2_1_3)) )) (PreH11 : (range l1_low_level_spec )) (PreH12 : ((INT_MIN) <= s_2)) (PreH13 : (s_2 <= INT_MAX)) (PreH14 : (glibc_slist_clean_iter_back_2_prev_case p lpre_2 node x_pre )) (PreH15 : (l2_1 = (cons (v) (lrest)))) (PreH16 : (x_pre <> 0)) (PreH17 : (x_pre <> st)) (PreH18 : (range (@nil Z) )) (PreH19 : (range l2_1 )) (PreH20 : (range (app ((@nil Z)) (l2_1)) )) (PreH21 : (range l1_low_level_spec )) (PreH22 : ((INT_MIN) <= s)) (PreH23 : (s <= INT_MAX)) (PreH24 : (glibc_slist_clean_iter_back_2_prev_case 0 (@nil Z) x_pre x_pre )) ,
  (sllseg x_pre node lpre_2 )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((node)  # "list" ->ₛ "data")) # Int  |-> v_3)
  **  (sllseg y_2 st_2 lrest_3 )
  **  (sllseg x_pre x_pre (@nil Z) )
|--
  EX (y: Z)  (lpre: (@list Z))  (v_2: Z)  (lrest_2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 ((cons (v_2) (lrest_2))) (s_2))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre) ((cons (v_2) (lrest_2))))) (ldone_2))) ((app (lpre) ((cons (v_2) (lrest_2))))) (s_2)))) X_low_level_spec ) ” 
  &&  “ (y_2 <> 0) ” 
  &&  “ (x_pre <> st_2) ” 
  &&  “ (range lpre ) ” 
  &&  “ (range (cons (v_2) (lrest_2)) ) ” 
  &&  “ (range (app (lpre) ((cons (v_2) (lrest_2)))) ) ” 
  &&  “ (range l1_low_level_spec ) ” 
  &&  “ ((INT_MIN) <= s_2) ” 
  &&  “ (s_2 <= INT_MAX) ” 
  &&  “ (glibc_slist_clean_iter_back_2_prev_case node lpre y_2 x_pre ) ” 
  &&  “ (l2_1 = (cons (v) (lrest))) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> st) ” 
  &&  “ (range (@nil Z) ) ” 
  &&  “ (range l2_1 ) ” 
  &&  “ (range (app ((@nil Z)) (l2_1)) ) ” 
  &&  “ (range l1_low_level_spec ) ” 
  &&  “ ((INT_MIN) <= s) ” 
  &&  “ (s <= INT_MAX) ” 
  &&  “ (glibc_slist_clean_iter_back_2_prev_case 0 (@nil Z) x_pre x_pre ) ”
  &&  (sllseg x_pre y_2 lpre )
  **  ((&((y_2)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((y_2)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  (sllseg y st_2 lrest_2 )
  **  (sllseg x_pre x_pre (@nil Z) )
).

Definition glibc_slist_clean_iter_back_2_entail_wit_5 := 
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st_2: Z) (s_2: Z) (l2_1: (@list Z)) (v_2: Z) (lrest: (@list Z)) (y_2: Z) (p: Z) (st: Z) (node: Z) (ldone_2: (@list Z)) (lpre_2: (@list Z)) (s: Z) (v_3: Z) (lrest_2: (@list Z)) (l2_1_2: (@list Z)) (PreH1 : (y_2 = st)) (PreH2 : (l2_1_2 = (cons (v_3) (lrest_2)))) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 (l2_1_2) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre_2) (l2_1_2))) (ldone_2))) ((app (lpre_2) (l2_1_2))) (s)))) X_low_level_spec )) (PreH4 : (node <> 0)) (PreH5 : (x_pre <> st)) (PreH6 : (range lpre_2 )) (PreH7 : (range l2_1_2 )) (PreH8 : (range (app (lpre_2) (l2_1_2)) )) (PreH9 : (range l1_low_level_spec )) (PreH10 : ((INT_MIN) <= s)) (PreH11 : (s <= INT_MAX)) (PreH12 : (glibc_slist_clean_iter_back_2_prev_case p lpre_2 node x_pre )) (PreH13 : (l2_1 = (cons (v_2) (lrest)))) (PreH14 : (x_pre <> 0)) (PreH15 : (x_pre <> st_2)) (PreH16 : (range (@nil Z) )) (PreH17 : (range l2_1 )) (PreH18 : (range (app ((@nil Z)) (l2_1)) )) (PreH19 : (range l1_low_level_spec )) (PreH20 : ((INT_MIN) <= s_2)) (PreH21 : (s_2 <= INT_MAX)) (PreH22 : (glibc_slist_clean_iter_back_2_prev_case 0 (@nil Z) x_pre x_pre )) ,
  (sllseg x_pre node lpre_2 )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((node)  # "list" ->ₛ "data")) # Int  |-> v_3)
  **  (sllseg y_2 st lrest_2 )
  **  (sll st ldone_2 )
  **  (sllseg x_pre x_pre (@nil Z) )
|--
  EX (ldone: (@list Z))  (lpre: (@list Z))  (v: Z)  (y: Z) ,
  “ (y = st) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 ((cons (v) ((@nil Z)))) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre) ((cons (v) ((@nil Z)))))) (ldone))) ((app (lpre) ((cons (v) ((@nil Z)))))) (s)))) X_low_level_spec ) ” 
  &&  “ (node <> 0) ” 
  &&  “ (range lpre ) ” 
  &&  “ (range (cons (v) ((@nil Z))) ) ” 
  &&  “ (range (app (lpre) ((cons (v) ((@nil Z))))) ) ” 
  &&  “ (range l1_low_level_spec ) ” 
  &&  “ ((INT_MIN) <= s) ” 
  &&  “ (s <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (s + v )) ” 
  &&  “ ((s + v ) <= INT_MAX) ” 
  &&  “ (glibc_slist_clean_iter_back_2_prev_case p lpre node x_pre ) ”
  &&  (sllseg x_pre node lpre )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sll y ldone )
) \/
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st_2: Z) (s_2: Z) (l2_1: (@list Z)) (v_2: Z) (lrest: (@list Z)) (y_2: Z) (p: Z) (st: Z) (node: Z) (ldone_2: (@list Z)) (lpre_2: (@list Z)) (s: Z) (v_3: Z) (lrest_2: (@list Z)) (l2_1_2: (@list Z)) (PreH1 : (y_2 = st)) (PreH2 : (l2_1_2 = (cons (v_3) (lrest_2)))) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 (l2_1_2) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre_2) (l2_1_2))) (ldone_2))) ((app (lpre_2) (l2_1_2))) (s)))) X_low_level_spec )) (PreH4 : (node <> 0)) (PreH5 : (x_pre <> st)) (PreH6 : (range lpre_2 )) (PreH7 : (range l2_1_2 )) (PreH8 : (range (app (lpre_2) (l2_1_2)) )) (PreH9 : (range l1_low_level_spec )) (PreH10 : ((INT_MIN) <= s)) (PreH11 : (s <= INT_MAX)) (PreH12 : (glibc_slist_clean_iter_back_2_prev_case p lpre_2 node x_pre )) (PreH13 : (l2_1 = (cons (v_2) (lrest)))) (PreH14 : (x_pre <> 0)) (PreH15 : (x_pre <> st_2)) (PreH16 : (range (@nil Z) )) (PreH17 : (range l2_1 )) (PreH18 : (range (app ((@nil Z)) (l2_1)) )) (PreH19 : (range l1_low_level_spec )) (PreH20 : ((INT_MIN) <= s_2)) (PreH21 : (s_2 <= INT_MAX)) (PreH22 : (glibc_slist_clean_iter_back_2_prev_case 0 (@nil Z) x_pre x_pre )) ,
  (sllseg y_2 st lrest_2 )
  **  (sllseg x_pre x_pre (@nil Z) )
|--
  “ ((s + v_3 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (s + v_3 )) ” 
  &&  “ (range (app (lpre_2) ((cons (v_3) ((@nil Z))))) ) ” 
  &&  “ (range (cons (v_3) ((@nil Z))) ) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 ((cons (v_3) ((@nil Z)))) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre_2) ((cons (v_3) ((@nil Z)))))) (ldone_2))) ((app (lpre_2) ((cons (v_3) ((@nil Z)))))) (s)))) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_iter_back_2_entail_wit_5_split_goal_1 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st_2: Z) (s_2: Z) (l2_1: (@list Z)) (v_2: Z) (lrest: (@list Z)) (y_2: Z) (p: Z) (st: Z) (node: Z) (ldone_2: (@list Z)) (lpre_2: (@list Z)) (s: Z) (v_3: Z) (lrest_2: (@list Z)) (l2_1_2: (@list Z)) (PreH1 : (y_2 = st)) (PreH2 : (l2_1_2 = (cons (v_3) (lrest_2)))) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 (l2_1_2) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre_2) (l2_1_2))) (ldone_2))) ((app (lpre_2) (l2_1_2))) (s)))) X_low_level_spec )) (PreH4 : (node <> 0)) (PreH5 : (x_pre <> st)) (PreH6 : (range lpre_2 )) (PreH7 : (range l2_1_2 )) (PreH8 : (range (app (lpre_2) (l2_1_2)) )) (PreH9 : (range l1_low_level_spec )) (PreH10 : ((INT_MIN) <= s)) (PreH11 : (s <= INT_MAX)) (PreH12 : (glibc_slist_clean_iter_back_2_prev_case p lpre_2 node x_pre )) (PreH13 : (l2_1 = (cons (v_2) (lrest)))) (PreH14 : (x_pre <> 0)) (PreH15 : (x_pre <> st_2)) (PreH16 : (range (@nil Z) )) (PreH17 : (range l2_1 )) (PreH18 : (range (app ((@nil Z)) (l2_1)) )) (PreH19 : (range l1_low_level_spec )) (PreH20 : ((INT_MIN) <= s_2)) (PreH21 : (s_2 <= INT_MAX)) (PreH22 : (glibc_slist_clean_iter_back_2_prev_case 0 (@nil Z) x_pre x_pre )) ,
  (sllseg y_2 st lrest_2 )
  **  (sllseg x_pre x_pre (@nil Z) )
|--
  “ ((s + v_3 ) <= INT_MAX) ”
.

Definition glibc_slist_clean_iter_back_2_entail_wit_5_split_goal_2 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st_2: Z) (s_2: Z) (l2_1: (@list Z)) (v_2: Z) (lrest: (@list Z)) (y_2: Z) (p: Z) (st: Z) (node: Z) (ldone_2: (@list Z)) (lpre_2: (@list Z)) (s: Z) (v_3: Z) (lrest_2: (@list Z)) (l2_1_2: (@list Z)) (PreH1 : (y_2 = st)) (PreH2 : (l2_1_2 = (cons (v_3) (lrest_2)))) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 (l2_1_2) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre_2) (l2_1_2))) (ldone_2))) ((app (lpre_2) (l2_1_2))) (s)))) X_low_level_spec )) (PreH4 : (node <> 0)) (PreH5 : (x_pre <> st)) (PreH6 : (range lpre_2 )) (PreH7 : (range l2_1_2 )) (PreH8 : (range (app (lpre_2) (l2_1_2)) )) (PreH9 : (range l1_low_level_spec )) (PreH10 : ((INT_MIN) <= s)) (PreH11 : (s <= INT_MAX)) (PreH12 : (glibc_slist_clean_iter_back_2_prev_case p lpre_2 node x_pre )) (PreH13 : (l2_1 = (cons (v_2) (lrest)))) (PreH14 : (x_pre <> 0)) (PreH15 : (x_pre <> st_2)) (PreH16 : (range (@nil Z) )) (PreH17 : (range l2_1 )) (PreH18 : (range (app ((@nil Z)) (l2_1)) )) (PreH19 : (range l1_low_level_spec )) (PreH20 : ((INT_MIN) <= s_2)) (PreH21 : (s_2 <= INT_MAX)) (PreH22 : (glibc_slist_clean_iter_back_2_prev_case 0 (@nil Z) x_pre x_pre )) ,
  (sllseg y_2 st lrest_2 )
  **  (sllseg x_pre x_pre (@nil Z) )
|--
  “ ((INT_MIN) <= (s + v_3 )) ”
.

Definition glibc_slist_clean_iter_back_2_entail_wit_5_split_goal_3 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st_2: Z) (s_2: Z) (l2_1: (@list Z)) (v_2: Z) (lrest: (@list Z)) (y_2: Z) (p: Z) (st: Z) (node: Z) (ldone_2: (@list Z)) (lpre_2: (@list Z)) (s: Z) (v_3: Z) (lrest_2: (@list Z)) (l2_1_2: (@list Z)) (PreH1 : (y_2 = st)) (PreH2 : (l2_1_2 = (cons (v_3) (lrest_2)))) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 (l2_1_2) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre_2) (l2_1_2))) (ldone_2))) ((app (lpre_2) (l2_1_2))) (s)))) X_low_level_spec )) (PreH4 : (node <> 0)) (PreH5 : (x_pre <> st)) (PreH6 : (range lpre_2 )) (PreH7 : (range l2_1_2 )) (PreH8 : (range (app (lpre_2) (l2_1_2)) )) (PreH9 : (range l1_low_level_spec )) (PreH10 : ((INT_MIN) <= s)) (PreH11 : (s <= INT_MAX)) (PreH12 : (glibc_slist_clean_iter_back_2_prev_case p lpre_2 node x_pre )) (PreH13 : (l2_1 = (cons (v_2) (lrest)))) (PreH14 : (x_pre <> 0)) (PreH15 : (x_pre <> st_2)) (PreH16 : (range (@nil Z) )) (PreH17 : (range l2_1 )) (PreH18 : (range (app ((@nil Z)) (l2_1)) )) (PreH19 : (range l1_low_level_spec )) (PreH20 : ((INT_MIN) <= s_2)) (PreH21 : (s_2 <= INT_MAX)) (PreH22 : (glibc_slist_clean_iter_back_2_prev_case 0 (@nil Z) x_pre x_pre )) ,
  (sllseg y_2 st lrest_2 )
  **  (sllseg x_pre x_pre (@nil Z) )
|--
  “ (range (app (lpre_2) ((cons (v_3) ((@nil Z))))) ) ”
.

Definition glibc_slist_clean_iter_back_2_entail_wit_5_split_goal_4 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st_2: Z) (s_2: Z) (l2_1: (@list Z)) (v_2: Z) (lrest: (@list Z)) (y_2: Z) (p: Z) (st: Z) (node: Z) (ldone_2: (@list Z)) (lpre_2: (@list Z)) (s: Z) (v_3: Z) (lrest_2: (@list Z)) (l2_1_2: (@list Z)) (PreH1 : (y_2 = st)) (PreH2 : (l2_1_2 = (cons (v_3) (lrest_2)))) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 (l2_1_2) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre_2) (l2_1_2))) (ldone_2))) ((app (lpre_2) (l2_1_2))) (s)))) X_low_level_spec )) (PreH4 : (node <> 0)) (PreH5 : (x_pre <> st)) (PreH6 : (range lpre_2 )) (PreH7 : (range l2_1_2 )) (PreH8 : (range (app (lpre_2) (l2_1_2)) )) (PreH9 : (range l1_low_level_spec )) (PreH10 : ((INT_MIN) <= s)) (PreH11 : (s <= INT_MAX)) (PreH12 : (glibc_slist_clean_iter_back_2_prev_case p lpre_2 node x_pre )) (PreH13 : (l2_1 = (cons (v_2) (lrest)))) (PreH14 : (x_pre <> 0)) (PreH15 : (x_pre <> st_2)) (PreH16 : (range (@nil Z) )) (PreH17 : (range l2_1 )) (PreH18 : (range (app ((@nil Z)) (l2_1)) )) (PreH19 : (range l1_low_level_spec )) (PreH20 : ((INT_MIN) <= s_2)) (PreH21 : (s_2 <= INT_MAX)) (PreH22 : (glibc_slist_clean_iter_back_2_prev_case 0 (@nil Z) x_pre x_pre )) ,
  (sllseg y_2 st lrest_2 )
  **  (sllseg x_pre x_pre (@nil Z) )
|--
  “ (range (cons (v_3) ((@nil Z))) ) ”
.

Definition glibc_slist_clean_iter_back_2_entail_wit_5_split_goal_5 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st_2: Z) (s_2: Z) (l2_1: (@list Z)) (v_2: Z) (lrest: (@list Z)) (y_2: Z) (p: Z) (st: Z) (node: Z) (ldone_2: (@list Z)) (lpre_2: (@list Z)) (s: Z) (v_3: Z) (lrest_2: (@list Z)) (l2_1_2: (@list Z)) (PreH1 : (y_2 = st)) (PreH2 : (l2_1_2 = (cons (v_3) (lrest_2)))) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 (l2_1_2) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre_2) (l2_1_2))) (ldone_2))) ((app (lpre_2) (l2_1_2))) (s)))) X_low_level_spec )) (PreH4 : (node <> 0)) (PreH5 : (x_pre <> st)) (PreH6 : (range lpre_2 )) (PreH7 : (range l2_1_2 )) (PreH8 : (range (app (lpre_2) (l2_1_2)) )) (PreH9 : (range l1_low_level_spec )) (PreH10 : ((INT_MIN) <= s)) (PreH11 : (s <= INT_MAX)) (PreH12 : (glibc_slist_clean_iter_back_2_prev_case p lpre_2 node x_pre )) (PreH13 : (l2_1 = (cons (v_2) (lrest)))) (PreH14 : (x_pre <> 0)) (PreH15 : (x_pre <> st_2)) (PreH16 : (range (@nil Z) )) (PreH17 : (range l2_1 )) (PreH18 : (range (app ((@nil Z)) (l2_1)) )) (PreH19 : (range l1_low_level_spec )) (PreH20 : ((INT_MIN) <= s_2)) (PreH21 : (s_2 <= INT_MAX)) (PreH22 : (glibc_slist_clean_iter_back_2_prev_case 0 (@nil Z) x_pre x_pre )) ,
  (sllseg y_2 st lrest_2 )
  **  (sllseg x_pre x_pre (@nil Z) )
|--
  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 ((cons (v_3) ((@nil Z)))) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre_2) ((cons (v_3) ((@nil Z)))))) (ldone_2))) ((app (lpre_2) ((cons (v_3) ((@nil Z)))))) (s)))) X_low_level_spec ) ”
.

Definition glibc_slist_clean_iter_back_2_entail_wit_5_split_goal_spatial := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st_2: Z) (s_2: Z) (l2_1: (@list Z)) (v_2: Z) (lrest: (@list Z)) (y_2: Z) (p: Z) (st: Z) (node: Z) (ldone_2: (@list Z)) (lpre_2: (@list Z)) (s: Z) (v_3: Z) (lrest_2: (@list Z)) (l2_1_2: (@list Z)) (PreH1 : (y_2 = st)) (PreH2 : (l2_1_2 = (cons (v_3) (lrest_2)))) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 (l2_1_2) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre_2) (l2_1_2))) (ldone_2))) ((app (lpre_2) (l2_1_2))) (s)))) X_low_level_spec )) (PreH4 : (node <> 0)) (PreH5 : (x_pre <> st)) (PreH6 : (range lpre_2 )) (PreH7 : (range l2_1_2 )) (PreH8 : (range (app (lpre_2) (l2_1_2)) )) (PreH9 : (range l1_low_level_spec )) (PreH10 : ((INT_MIN) <= s)) (PreH11 : (s <= INT_MAX)) (PreH12 : (glibc_slist_clean_iter_back_2_prev_case p lpre_2 node x_pre )) (PreH13 : (l2_1 = (cons (v_2) (lrest)))) (PreH14 : (x_pre <> 0)) (PreH15 : (x_pre <> st_2)) (PreH16 : (range (@nil Z) )) (PreH17 : (range l2_1 )) (PreH18 : (range (app ((@nil Z)) (l2_1)) )) (PreH19 : (range l1_low_level_spec )) (PreH20 : ((INT_MIN) <= s_2)) (PreH21 : (s_2 <= INT_MAX)) (PreH22 : (glibc_slist_clean_iter_back_2_prev_case 0 (@nil Z) x_pre x_pre )) ,
  (sllseg y_2 st lrest_2 )
  **  (sllseg x_pre x_pre (@nil Z) )
|--
  TT && emp 
.

Definition glibc_slist_clean_iter_back_2_entail_wit_6 := 
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (p: Z) (st: Z) (s: Z) (lpre: (@list Z)) (ldone_2: (@list Z)) (y: Z) (v: Z) (node: Z) (PreH1 : (p = 0)) (PreH2 : (y = st)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 ((cons (v) ((@nil Z)))) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre) ((cons (v) ((@nil Z)))))) (ldone_2))) ((app (lpre) ((cons (v) ((@nil Z)))))) (s)))) X_low_level_spec )) (PreH4 : (node <> 0)) (PreH5 : (range lpre )) (PreH6 : (range (cons (v) ((@nil Z))) )) (PreH7 : (range (app (lpre) ((cons (v) ((@nil Z))))) )) (PreH8 : (range l1_low_level_spec )) (PreH9 : ((INT_MIN) <= s)) (PreH10 : (s <= INT_MAX)) (PreH11 : ((INT_MIN) <= (s + v ))) (PreH12 : ((s + v ) <= INT_MAX)) (PreH13 : (glibc_slist_clean_iter_back_2_prev_case p lpre node x_pre )) ,
  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((( &( "prev" ) )) # Ptr  |-> p)
  **  ((( &( "stop" ) )) # Ptr  |-> node)
  **  (sllseg x_pre node lpre )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sll y ldone_2 )
|--
  EX (v_2: Z)  (ldone: (@list Z)) ,
  “ (safeExec ATrue (return ((maketuple ((cons (v_2) (ldone))) ((s + v ))))) X_low_level_spec ) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((( &( "node" ) )) # Ptr  |-> x_pre)
  **  ((( &( "prev" ) )) # Ptr  |-> 0)
  **  ((( &( "stop" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre (cons (v_2) (ldone)) )
) \/
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (p: Z) (st: Z) (s: Z) (lpre: (@list Z)) (ldone_2: (@list Z)) (y: Z) (v: Z) (node: Z) (PreH1 : (v <= INT_MAX)) (PreH2 : (v >= INT_MIN)) (PreH3 : (p = 0)) (PreH4 : (y = st)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 ((cons (v) ((@nil Z)))) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre) ((cons (v) ((@nil Z)))))) (ldone_2))) ((app (lpre) ((cons (v) ((@nil Z)))))) (s)))) X_low_level_spec )) (PreH6 : (node <> 0)) (PreH7 : (range lpre )) (PreH8 : (range (cons (v) ((@nil Z))) )) (PreH9 : (range (app (lpre) ((cons (v) ((@nil Z))))) )) (PreH10 : (range l1_low_level_spec )) (PreH11 : ((INT_MIN) <= s)) (PreH12 : (s <= INT_MAX)) (PreH13 : ((INT_MIN) <= (s + v ))) (PreH14 : ((s + v ) <= INT_MAX)) (PreH15 : (glibc_slist_clean_iter_back_2_prev_case p lpre node x_pre )) ,
  (sllseg x_pre node lpre )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sll y ldone_2 )
|--
  EX (y_2: Z)  (v_2: Z)  (ldone: (@list Z)) ,
  “ (x_pre <> 0) ” 
  &&  “ (p = 0) ” 
  &&  “ (node = x_pre) ” 
  &&  “ (safeExec ATrue (return ((maketuple ((cons (v_2) (ldone))) ((s + v ))))) X_low_level_spec ) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sll y_2 ldone )
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v_2)
).

Definition glibc_slist_clean_iter_back_2_entail_wit_7 := 
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (p: Z) (st: Z) (s: Z) (lpre: (@list Z)) (ldone_2: (@list Z)) (y: Z) (v: Z) (node: Z) (PreH1 : (p <> 0)) (PreH2 : (y = st)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 ((cons (v) ((@nil Z)))) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre) ((cons (v) ((@nil Z)))))) (ldone_2))) ((app (lpre) ((cons (v) ((@nil Z)))))) (s)))) X_low_level_spec )) (PreH4 : (node <> 0)) (PreH5 : (range lpre )) (PreH6 : (range (cons (v) ((@nil Z))) )) (PreH7 : (range (app (lpre) ((cons (v) ((@nil Z))))) )) (PreH8 : (range l1_low_level_spec )) (PreH9 : ((INT_MIN) <= s)) (PreH10 : (s <= INT_MAX)) (PreH11 : ((INT_MIN) <= (s + v ))) (PreH12 : ((s + v ) <= INT_MAX)) (PreH13 : (glibc_slist_clean_iter_back_2_prev_case p lpre node x_pre )) ,
  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((( &( "prev" ) )) # Ptr  |-> p)
  **  (sllseg x_pre node lpre )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sll y ldone_2 )
|--
  EX (l1_1: (@list Z))  (ldone: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop1 (l1_1) ((s + v )))) ((glibc_slist_clean_iter_back_2_M_loop1_end ((app (l1_1) (ldone)))))) X_low_level_spec ) ” 
  &&  “ (range l1_1 ) ” 
  &&  “ ((INT_MIN) <= (s + v )) ” 
  &&  “ ((s + v ) <= INT_MAX) ” 
  &&  “ (range l1_low_level_spec ) ”
  &&  ((( &( "prev" ) )) # Ptr  |->_)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x_pre node l1_1 )
  **  (sll node ldone )
) \/
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (p: Z) (st: Z) (s: Z) (lpre: (@list Z)) (ldone_2: (@list Z)) (y: Z) (v: Z) (node: Z) (PreH1 : (p <> 0)) (PreH2 : (y = st)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 ((cons (v) ((@nil Z)))) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre) ((cons (v) ((@nil Z)))))) (ldone_2))) ((app (lpre) ((cons (v) ((@nil Z)))))) (s)))) X_low_level_spec )) (PreH4 : (node <> 0)) (PreH5 : (range lpre )) (PreH6 : (range (cons (v) ((@nil Z))) )) (PreH7 : (range (app (lpre) ((cons (v) ((@nil Z))))) )) (PreH8 : (range l1_low_level_spec )) (PreH9 : ((INT_MIN) <= s)) (PreH10 : (s <= INT_MAX)) (PreH11 : ((INT_MIN) <= (s + v ))) (PreH12 : ((s + v ) <= INT_MAX)) (PreH13 : (glibc_slist_clean_iter_back_2_prev_case p lpre node x_pre )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop1 (lpre) ((s + v )))) ((glibc_slist_clean_iter_back_2_M_loop1_end ((app (lpre) ((cons (v) (ldone_2)))))))) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_iter_back_2_entail_wit_7_split_goal_1 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (p: Z) (st: Z) (s: Z) (lpre: (@list Z)) (ldone_2: (@list Z)) (y: Z) (v: Z) (node: Z) (PreH1 : (p <> 0)) (PreH2 : (y = st)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop2 ((cons (v) ((@nil Z)))) (s))) ((glibc_slist_clean_iter_back_2_M_loop2_cont ((app ((app (lpre) ((cons (v) ((@nil Z)))))) (ldone_2))) ((app (lpre) ((cons (v) ((@nil Z)))))) (s)))) X_low_level_spec )) (PreH4 : (node <> 0)) (PreH5 : (range lpre )) (PreH6 : (range (cons (v) ((@nil Z))) )) (PreH7 : (range (app (lpre) ((cons (v) ((@nil Z))))) )) (PreH8 : (range l1_low_level_spec )) (PreH9 : ((INT_MIN) <= s)) (PreH10 : (s <= INT_MAX)) (PreH11 : ((INT_MIN) <= (s + v ))) (PreH12 : ((s + v ) <= INT_MAX)) (PreH13 : (glibc_slist_clean_iter_back_2_prev_case p lpre node x_pre )) ,
  (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop1 (lpre) ((s + v )))) ((glibc_slist_clean_iter_back_2_M_loop1_end ((app (lpre) ((cons (v) (ldone_2)))))))) X_low_level_spec )
.

Definition glibc_slist_clean_iter_back_2_return_wit_1 := 
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st: Z) (s: Z) (l1_1: (@list Z)) (ldone: (@list Z)) (PreH1 : (x_pre = st)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop1 (l1_1) (s))) ((glibc_slist_clean_iter_back_2_M_loop1_end ((app (l1_1) (ldone)))))) X_low_level_spec )) (PreH3 : (range l1_1 )) (PreH4 : ((INT_MIN) <= s)) (PreH5 : (s <= INT_MAX)) (PreH6 : (range l1_low_level_spec )) ,
  (sllseg x_pre st l1_1 )
  **  (sll st ldone )
|--
  EX (l2: (@list Z))  (r: Z) ,
  “ (safeExec ATrue (return ((maketuple (l2) (r)))) X_low_level_spec ) ” 
  &&  “ (s = r) ”
  &&  (sll x_pre l2 )
) \/
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st: Z) (s: Z) (l1_1: (@list Z)) (ldone: (@list Z)) (PreH1 : (x_pre = st)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop1 (l1_1) (s))) ((glibc_slist_clean_iter_back_2_M_loop1_end ((app (l1_1) (ldone)))))) X_low_level_spec )) (PreH3 : (range l1_1 )) (PreH4 : ((INT_MIN) <= s)) (PreH5 : (s <= INT_MAX)) (PreH6 : (range l1_low_level_spec )) ,
  (sllseg x_pre st l1_1 )
|--
  “ (safeExec ATrue (return ((maketuple (ldone) (s)))) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_iter_back_2_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st: Z) (s: Z) (l1_1: (@list Z)) (ldone: (@list Z)) (PreH1 : (x_pre = st)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop1 (l1_1) (s))) ((glibc_slist_clean_iter_back_2_M_loop1_end ((app (l1_1) (ldone)))))) X_low_level_spec )) (PreH3 : (range l1_1 )) (PreH4 : ((INT_MIN) <= s)) (PreH5 : (s <= INT_MAX)) (PreH6 : (range l1_low_level_spec )) ,
  (sllseg x_pre st l1_1 )
|--
  “ (safeExec ATrue (return ((maketuple (ldone) (s)))) X_low_level_spec ) ”
.

Definition glibc_slist_clean_iter_back_2_return_wit_1_split_goal_spatial := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (st: Z) (s: Z) (l1_1: (@list Z)) (ldone: (@list Z)) (PreH1 : (x_pre = st)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_2_M_loop1 (l1_1) (s))) ((glibc_slist_clean_iter_back_2_M_loop1_end ((app (l1_1) (ldone)))))) X_low_level_spec )) (PreH3 : (range l1_1 )) (PreH4 : ((INT_MIN) <= s)) (PreH5 : (s <= INT_MAX)) (PreH6 : (range l1_low_level_spec )) ,
  (sllseg x_pre st l1_1 )
|--
  TT && emp 
.

Definition glibc_slist_clean_iter_back_2_return_wit_2 := 
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (ldone: (@list Z)) (v: Z) (sum: Z) (PreH1 : (safeExec ATrue (return ((maketuple ((cons (v) (ldone))) (sum)))) X_low_level_spec )) (PreH2 : (x_pre <> 0)) ,
  (sll x_pre (cons (v) (ldone)) )
|--
  EX (l2: (@list Z))  (r: Z) ,
  “ (safeExec ATrue (return ((maketuple (l2) (r)))) X_low_level_spec ) ” 
  &&  “ (sum = r) ”
  &&  (sll x_pre l2 )
.

Definition glibc_slist_clean_iter_back_2_derive_high_level_spec_by_low_level_spec := 
forall (x_pre: Z) (l1_high_level_spec: (@list Z)) ,
  “ (range l1_high_level_spec ) ”
  &&  (sllseg x_pre 0 l1_high_level_spec )
|--
EX (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (l1_low_level_spec: (@list Z)) ,
  (“ (range l1_low_level_spec ) ” 
  &&  “ (safeExec ATrue (glibc_slist_clean_iter_back_2_M (l1_low_level_spec)) X_low_level_spec ) ”
  &&  (sllseg x_pre 0 l1_low_level_spec ))
  **
  ((EX l2 r retval_2,
  “ (safeExec ATrue (return ((maketuple (l2) (r)))) X_low_level_spec ) ” 
  &&  “ (retval_2 = r) ”
  &&  (sll x_pre l2 ))
  -*
  (EX retval,
  “ (retval = (list_sum (l1_high_level_spec))) ”
  &&  (sll x_pre l1_high_level_spec )))
.

Module Type VC_Correct.

Include safeexecE_Strategy_Correct.
Include sll_Strategy_Correct.

Axiom proof_of_glibc_slist_clean_iter_back_2_safety_wit_1 : glibc_slist_clean_iter_back_2_safety_wit_1.
Axiom proof_of_glibc_slist_clean_iter_back_2_safety_wit_2 : glibc_slist_clean_iter_back_2_safety_wit_2.
Axiom proof_of_glibc_slist_clean_iter_back_2_safety_wit_3 : glibc_slist_clean_iter_back_2_safety_wit_3.
Axiom proof_of_glibc_slist_clean_iter_back_2_safety_wit_4 : glibc_slist_clean_iter_back_2_safety_wit_4.
Axiom proof_of_glibc_slist_clean_iter_back_2_safety_wit_5 : glibc_slist_clean_iter_back_2_safety_wit_5.
Axiom proof_of_glibc_slist_clean_iter_back_2_entail_wit_1 : glibc_slist_clean_iter_back_2_entail_wit_1.
Axiom proof_of_glibc_slist_clean_iter_back_2_entail_wit_2 : glibc_slist_clean_iter_back_2_entail_wit_2.
Axiom proof_of_glibc_slist_clean_iter_back_2_entail_wit_3 : glibc_slist_clean_iter_back_2_entail_wit_3.
Axiom proof_of_glibc_slist_clean_iter_back_2_entail_wit_4 : glibc_slist_clean_iter_back_2_entail_wit_4.
Axiom proof_of_glibc_slist_clean_iter_back_2_entail_wit_5 : glibc_slist_clean_iter_back_2_entail_wit_5.
Axiom proof_of_glibc_slist_clean_iter_back_2_entail_wit_6 : glibc_slist_clean_iter_back_2_entail_wit_6.
Axiom proof_of_glibc_slist_clean_iter_back_2_entail_wit_7 : glibc_slist_clean_iter_back_2_entail_wit_7.
Axiom proof_of_glibc_slist_clean_iter_back_2_return_wit_1 : glibc_slist_clean_iter_back_2_return_wit_1.
Axiom proof_of_glibc_slist_clean_iter_back_2_return_wit_2 : glibc_slist_clean_iter_back_2_return_wit_2.
Axiom proof_of_glibc_slist_clean_iter_back_2_derive_high_level_spec_by_low_level_spec : glibc_slist_clean_iter_back_2_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
