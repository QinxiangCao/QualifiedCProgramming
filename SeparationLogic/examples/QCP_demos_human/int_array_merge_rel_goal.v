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
From MonadLib.StateRelMonad Require Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import SimpleC.EE.QCP_demos_human.int_array_merge_rel_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_human Require Import safeexec_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import safeexec_strategy_proof.

(*----- Function merge -----*)

Definition merge_safety_wit_1 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l0: (@list Z)) (s2: (@list Z)) (s1: (@list Z)) (PreH1 : (safeExec ATrue (merge_rel (s1) (s2)) X )) (PreH2 : (0 <= p_pre)) (PreH3 : (p_pre <= q_pre)) (PreH4 : (q_pre < r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> p_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.seg arr_pre p_pre (q_pre + 1 ) s1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) (r_pre + 1 ) s2 )
  **  (IntArray.seg ret_pre p_pre (r_pre + 1 ) l0 )
|--
  “ ((q_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (q_pre + 1 )) ”
.

Definition merge_safety_wit_2 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l0: (@list Z)) (s2: (@list Z)) (s1: (@list Z)) (PreH1 : (safeExec ATrue (merge_rel (s1) (s2)) X )) (PreH2 : (0 <= p_pre)) (PreH3 : (p_pre <= q_pre)) (PreH4 : (q_pre < r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> p_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.seg arr_pre p_pre (q_pre + 1 ) s1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) (r_pre + 1 ) s2 )
  **  (IntArray.seg ret_pre p_pre (r_pre + 1 ) l0 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition merge_safety_wit_3 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH2 : (p_pre <= i)) (PreH3 : ((q_pre + 1 ) <= j)) (PreH4 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH5 : (0 <= p_pre)) (PreH6 : (p_pre <= q_pre)) (PreH7 : (q_pre < r_pre)) (PreH8 : ((r_pre + 1 ) <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ ((q_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (q_pre + 1 )) ”
.

Definition merge_safety_wit_4 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH2 : (p_pre <= i)) (PreH3 : ((q_pre + 1 ) <= j)) (PreH4 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH5 : (0 <= p_pre)) (PreH6 : (p_pre <= q_pre)) (PreH7 : (q_pre < r_pre)) (PreH8 : ((r_pre + 1 ) <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition merge_safety_wit_5 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (i < (q_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH3 : (p_pre <= i)) (PreH4 : ((q_pre + 1 ) <= j)) (PreH5 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= q_pre)) (PreH8 : (q_pre < r_pre)) (PreH9 : ((r_pre + 1 ) <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r_pre + 1 )) ”
.

Definition merge_safety_wit_6 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (i < (q_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH3 : (p_pre <= i)) (PreH4 : ((q_pre + 1 ) <= j)) (PreH5 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= q_pre)) (PreH8 : (q_pre < r_pre)) (PreH9 : ((r_pre + 1 ) <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition merge_safety_wit_7 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth (i - i ) l1 0) <= (Znth (j - j ) l2 0))) (PreH2 : (j < (r_pre + 1 ))) (PreH3 : (i < (q_pre + 1 ))) (PreH4 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH5 : (p_pre <= i)) (PreH6 : ((q_pre + 1 ) <= j)) (PreH7 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= q_pre)) (PreH10 : (q_pre < r_pre)) (PreH11 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg ret_pre k (r_pre + 1 ) (replace_Znth ((k - k )) ((Znth (i - i ) l1 0)) (l6)) )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg ret_pre p_pre k l3 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition merge_safety_wit_8 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth (i - i ) l1 0) > (Znth (j - j ) l2 0))) (PreH2 : (j < (r_pre + 1 ))) (PreH3 : (i < (q_pre + 1 ))) (PreH4 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH5 : (p_pre <= i)) (PreH6 : ((q_pre + 1 ) <= j)) (PreH7 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= q_pre)) (PreH10 : (q_pre < r_pre)) (PreH11 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg ret_pre k (r_pre + 1 ) (replace_Znth ((k - k )) ((Znth (j - j ) l2 0)) (l6)) )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg ret_pre p_pre k l3 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition merge_safety_wit_9 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth (i - i ) l1 0) <= (Znth (j - j ) l2 0))) (PreH2 : (j < (r_pre + 1 ))) (PreH3 : (i < (q_pre + 1 ))) (PreH4 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH5 : (p_pre <= i)) (PreH6 : ((q_pre + 1 ) <= j)) (PreH7 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= q_pre)) (PreH10 : (q_pre < r_pre)) (PreH11 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg ret_pre k (r_pre + 1 ) (replace_Znth ((k - k )) ((Znth (i - i ) l1 0)) (l6)) )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg ret_pre p_pre k l3 )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition merge_safety_wit_10 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth (i - i ) l1 0) > (Znth (j - j ) l2 0))) (PreH2 : (j < (r_pre + 1 ))) (PreH3 : (i < (q_pre + 1 ))) (PreH4 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH5 : (p_pre <= i)) (PreH6 : ((q_pre + 1 ) <= j)) (PreH7 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= q_pre)) (PreH10 : (q_pre < r_pre)) (PreH11 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg ret_pre k (r_pre + 1 ) (replace_Znth ((k - k )) ((Znth (j - j ) l2 0)) (l6)) )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg ret_pre p_pre k l3 )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition merge_safety_wit_11 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH2 : (0 <= p_pre)) (PreH3 : (p_pre <= q_pre)) (PreH4 : (q_pre < r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) (PreH6 : (p_pre <= i)) (PreH7 : ((q_pre + 1 ) <= j)) (PreH8 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH9 : (j = (r_pre + 1 ))) ,
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ ((q_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (q_pre + 1 )) ”
.

Definition merge_safety_wit_12 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH2 : (0 <= p_pre)) (PreH3 : (p_pre <= q_pre)) (PreH4 : (q_pre < r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) (PreH6 : (p_pre <= i)) (PreH7 : ((q_pre + 1 ) <= j)) (PreH8 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH9 : (i = (q_pre + 1 ))) ,
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ ((q_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (q_pre + 1 )) ”
.

Definition merge_safety_wit_13 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH2 : (0 <= p_pre)) (PreH3 : (p_pre <= q_pre)) (PreH4 : (q_pre < r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) (PreH6 : (p_pre <= i)) (PreH7 : ((q_pre + 1 ) <= j)) (PreH8 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH9 : (i = (q_pre + 1 ))) ,
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition merge_safety_wit_14 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH2 : (0 <= p_pre)) (PreH3 : (p_pre <= q_pre)) (PreH4 : (q_pre < r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) (PreH6 : (p_pre <= i)) (PreH7 : ((q_pre + 1 ) <= j)) (PreH8 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH9 : (j = (r_pre + 1 ))) ,
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition merge_safety_wit_15 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (i < (q_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (i = (q_pre + 1 ))) ,
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ False ”
.

Definition merge_safety_wit_16 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (i < (q_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (j = (r_pre + 1 ))) ,
  (IntArray.seg ret_pre k (r_pre + 1 ) (replace_Znth ((k - k )) ((Znth (i - i ) l1 0)) (l6)) )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition merge_safety_wit_17 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (i < (q_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (j = (r_pre + 1 ))) ,
  (IntArray.seg ret_pre k (r_pre + 1 ) (replace_Znth ((k - k )) ((Znth (i - i ) l1 0)) (l6)) )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition merge_safety_wit_18 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2) (l3)) X )) (PreH2 : (0 <= p_pre)) (PreH3 : (p_pre <= q_pre)) (PreH4 : (q_pre < r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) (PreH6 : (p_pre <= i)) (PreH7 : ((q_pre + 1 ) <= j)) (PreH8 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH9 : (i = (q_pre + 1 ))) ,
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r_pre + 1 )) ”
.

Definition merge_safety_wit_19 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2) (l3)) X )) (PreH2 : (0 <= p_pre)) (PreH3 : (p_pre <= q_pre)) (PreH4 : (q_pre < r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) (PreH6 : (p_pre <= i)) (PreH7 : ((q_pre + 1 ) <= j)) (PreH8 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH9 : (i = (q_pre + 1 ))) ,
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition merge_safety_wit_20 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (j < (r_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2) (l3)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (i = (q_pre + 1 ))) ,
  (IntArray.seg ret_pre k (r_pre + 1 ) (replace_Znth ((k - k )) ((Znth (j - j ) l2 0)) (l6)) )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg ret_pre p_pre k l3 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition merge_safety_wit_21 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (j < (r_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2) (l3)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (i = (q_pre + 1 ))) ,
  (IntArray.seg ret_pre k (r_pre + 1 ) (replace_Znth ((k - k )) ((Znth (j - j ) l2 0)) (l6)) )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg ret_pre p_pre k l3 )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition merge_entail_wit_1 := 
(
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l0: (@list Z)) (s2: (@list Z)) (s1: (@list Z)) (PreH1 : (safeExec ATrue (merge_rel (s1) (s2)) X )) (PreH2 : (0 <= p_pre)) (PreH3 : (p_pre <= q_pre)) (PreH4 : (q_pre < r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg arr_pre p_pre (q_pre + 1 ) s1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) (r_pre + 1 ) s2 )
  **  (IntArray.seg ret_pre p_pre (r_pre + 1 ) l0 )
|--
  EX (l6: (@list Z))  (l5: (@list Z))  (l4: (@list Z))  (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ” 
  &&  “ (p_pre <= p_pre) ” 
  &&  “ ((q_pre + 1 ) <= (q_pre + 1 )) ” 
  &&  “ (p_pre = ((p_pre + (p_pre - p_pre ) ) + ((q_pre + 1 ) - (q_pre + 1 ) ) )) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ”
  &&  (IntArray.seg arr_pre p_pre p_pre l4 )
  **  (IntArray.seg arr_pre p_pre (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) (q_pre + 1 ) l5 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre p_pre l3 )
  **  (IntArray.seg ret_pre p_pre (r_pre + 1 ) l6 )
) \/
(
forall (r_pre: Z) (q_pre: Z) (p_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (s2: (@list Z)) (s1: (@list Z)) (PreH1 : (safeExec ATrue (merge_rel (s1) (s2)) X )) (PreH2 : (0 <= p_pre)) (PreH3 : (p_pre <= q_pre)) (PreH4 : (q_pre < r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) ,
  TT && emp 
|--
  “ (safeExec ATrue (merge_from_mid_rel (s1) (s2) ((@nil Z))) X ) ”
  &&  emp
).

Definition merge_entail_wit_1_split_goal_1 := 
forall (r_pre: Z) (q_pre: Z) (p_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (s2: (@list Z)) (s1: (@list Z)) (PreH1 : (safeExec ATrue (merge_rel (s1) (s2)) X )) (PreH2 : (0 <= p_pre)) (PreH3 : (p_pre <= q_pre)) (PreH4 : (q_pre < r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) ,
  (safeExec ATrue (merge_from_mid_rel (s1) (s2) ((@nil Z))) X )
.

Definition merge_entail_wit_2_1 := 
(
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6_2: (@list Z)) (l5_2: (@list Z)) (l4_2: (@list Z)) (k: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : ((Znth (i - i ) l1_2 0) <= (Znth (j - j ) l2_2 0))) (PreH2 : (j < (r_pre + 1 ))) (PreH3 : (i < (q_pre + 1 ))) (PreH4 : (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X )) (PreH5 : (p_pre <= i)) (PreH6 : ((q_pre + 1 ) <= j)) (PreH7 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= q_pre)) (PreH10 : (q_pre < r_pre)) (PreH11 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg ret_pre k (r_pre + 1 ) (replace_Znth ((k - k )) ((Znth (i - i ) l1_2 0)) (l6_2)) )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1_2 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2_2 )
  **  (IntArray.seg arr_pre p_pre i l4_2 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5_2 )
  **  (IntArray.seg ret_pre p_pre k l3_2 )
|--
  EX (l6: (@list Z))  (l5: (@list Z))  (l4: (@list Z))  (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ” 
  &&  “ (p_pre <= (i + 1 )) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ ((k + 1 ) = ((p_pre + ((i + 1 ) - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ”
  &&  (IntArray.seg arr_pre p_pre (i + 1 ) l4 )
  **  (IntArray.seg arr_pre (i + 1 ) (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre (k + 1 ) l3 )
  **  (IntArray.seg ret_pre (k + 1 ) (r_pre + 1 ) l6 )
) \/
(
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6_2: (@list Z)) (l4_2: (@list Z)) (k: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : ((Znth (i - i ) l1_2 0) <= (Znth (j - j ) l2_2 0))) (PreH2 : (j < (r_pre + 1 ))) (PreH3 : (i < (q_pre + 1 ))) (PreH4 : (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X )) (PreH5 : (p_pre <= i)) (PreH6 : ((q_pre + 1 ) <= j)) (PreH7 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= q_pre)) (PreH10 : (q_pre < r_pre)) (PreH11 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg ret_pre k (r_pre + 1 ) (replace_Znth ((k - k )) ((Znth (i - i ) l1_2 0)) (l6_2)) )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1_2 )
  **  (IntArray.seg arr_pre p_pre i l4_2 )
  **  (IntArray.seg ret_pre p_pre k l3_2 )
|--
  EX (l6: (@list Z))  (l4: (@list Z))  (l1: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2_2) (l3)) X ) ” 
  &&  “ (p_pre <= (i + 1 )) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ ((k + 1 ) = ((p_pre + ((i + 1 ) - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ”
  &&  (IntArray.seg arr_pre p_pre (i + 1 ) l4 )
  **  (IntArray.seg arr_pre (i + 1 ) (q_pre + 1 ) l1 )
  **  (IntArray.seg ret_pre p_pre (k + 1 ) l3 )
  **  (IntArray.seg ret_pre (k + 1 ) (r_pre + 1 ) l6 )
).

Definition merge_entail_wit_2_2 := 
(
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6_2: (@list Z)) (l5_2: (@list Z)) (l4_2: (@list Z)) (k: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : ((Znth (i - i ) l1_2 0) > (Znth (j - j ) l2_2 0))) (PreH2 : (j < (r_pre + 1 ))) (PreH3 : (i < (q_pre + 1 ))) (PreH4 : (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X )) (PreH5 : (p_pre <= i)) (PreH6 : ((q_pre + 1 ) <= j)) (PreH7 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= q_pre)) (PreH10 : (q_pre < r_pre)) (PreH11 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg ret_pre k (r_pre + 1 ) (replace_Znth ((k - k )) ((Znth (j - j ) l2_2 0)) (l6_2)) )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2_2 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1_2 )
  **  (IntArray.seg arr_pre p_pre i l4_2 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5_2 )
  **  (IntArray.seg ret_pre p_pre k l3_2 )
|--
  EX (l6: (@list Z))  (l5: (@list Z))  (l4: (@list Z))  (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= (j + 1 )) ” 
  &&  “ ((k + 1 ) = ((p_pre + (i - p_pre ) ) + ((j + 1 ) - (q_pre + 1 ) ) )) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ”
  &&  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) (j + 1 ) l5 )
  **  (IntArray.seg arr_pre (j + 1 ) (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre (k + 1 ) l3 )
  **  (IntArray.seg ret_pre (k + 1 ) (r_pre + 1 ) l6 )
) \/
(
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6_2: (@list Z)) (l5_2: (@list Z)) (k: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : ((Znth (i - i ) l1_2 0) > (Znth (j - j ) l2_2 0))) (PreH2 : (j < (r_pre + 1 ))) (PreH3 : (i < (q_pre + 1 ))) (PreH4 : (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X )) (PreH5 : (p_pre <= i)) (PreH6 : ((q_pre + 1 ) <= j)) (PreH7 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= q_pre)) (PreH10 : (q_pre < r_pre)) (PreH11 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg ret_pre k (r_pre + 1 ) (replace_Znth ((k - k )) ((Znth (j - j ) l2_2 0)) (l6_2)) )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2_2 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5_2 )
  **  (IntArray.seg ret_pre p_pre k l3_2 )
|--
  EX (l6: (@list Z))  (l5: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (merge_from_mid_rel (l1_2) (l2) (l3)) X ) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= (j + 1 )) ” 
  &&  “ ((k + 1 ) = ((p_pre + (i - p_pre ) ) + ((j + 1 ) - (q_pre + 1 ) ) )) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ”
  &&  (IntArray.seg arr_pre (q_pre + 1 ) (j + 1 ) l5 )
  **  (IntArray.seg arr_pre (j + 1 ) (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre (k + 1 ) l3 )
  **  (IntArray.seg ret_pre (k + 1 ) (r_pre + 1 ) l6 )
).

Definition merge_entail_wit_3_1 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6_2: (@list Z)) (l5_2: (@list Z)) (l4_2: (@list Z)) (k: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (i >= (q_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X )) (PreH3 : (p_pre <= i)) (PreH4 : ((q_pre + 1 ) <= j)) (PreH5 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= q_pre)) (PreH8 : (q_pre < r_pre)) (PreH9 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg arr_pre p_pre i l4_2 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1_2 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5_2 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2_2 )
  **  (IntArray.seg ret_pre p_pre k l3_2 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6_2 )
|--
  (EX (l6: (@list Z))  (l5: (@list Z))  (l4: (@list Z))  (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ (i = (q_pre + 1 )) ”
  &&  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 ))
  ||
  (EX (l6: (@list Z))  (l5: (@list Z))  (l4: (@list Z))  (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ (j = (r_pre + 1 )) ”
  &&  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 ))
.

Definition merge_entail_wit_3_2 := 
(
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6_2: (@list Z)) (l5_2: (@list Z)) (l4_2: (@list Z)) (k: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (j >= (r_pre + 1 ))) (PreH2 : (i < (q_pre + 1 ))) (PreH3 : (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X )) (PreH4 : (p_pre <= i)) (PreH5 : ((q_pre + 1 ) <= j)) (PreH6 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= q_pre)) (PreH9 : (q_pre < r_pre)) (PreH10 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg arr_pre p_pre i l4_2 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1_2 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5_2 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2_2 )
  **  (IntArray.seg ret_pre p_pre k l3_2 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6_2 )
|--
  EX (l6: (@list Z))  (l5: (@list Z))  (l4: (@list Z))  (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ (j = (r_pre + 1 )) ”
  &&  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
) \/
(
forall (r_pre: Z) (q_pre: Z) (p_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (k: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (j >= (r_pre + 1 ))) (PreH2 : (i < (q_pre + 1 ))) (PreH3 : (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X )) (PreH4 : (p_pre <= i)) (PreH5 : ((q_pre + 1 ) <= j)) (PreH6 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= q_pre)) (PreH9 : (q_pre < r_pre)) (PreH10 : ((r_pre + 1 ) <= INT_MAX)) ,
  TT && emp 
|--
  “ (j = (r_pre + 1 )) ”
  &&  emp
).

Definition merge_entail_wit_3_2_split_goal_1 := 
forall (r_pre: Z) (q_pre: Z) (p_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (k: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (j >= (r_pre + 1 ))) (PreH2 : (i < (q_pre + 1 ))) (PreH3 : (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X )) (PreH4 : (p_pre <= i)) (PreH5 : ((q_pre + 1 ) <= j)) (PreH6 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= q_pre)) (PreH9 : (q_pre < r_pre)) (PreH10 : ((r_pre + 1 ) <= INT_MAX)) ,
  (j = (r_pre + 1 ))
.

Definition merge_entail_wit_4 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6_2: (@list Z)) (l5_2: (@list Z)) (l4_2: (@list Z)) (k: Z) (j: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (i < (q_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (j = (r_pre + 1 ))) ,
  (IntArray.seg ret_pre k (r_pre + 1 ) (replace_Znth ((k - k )) ((Znth (i - i ) l1_2 0)) (l6_2)) )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1_2 )
  **  (IntArray.seg arr_pre p_pre i l4_2 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5_2 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2_2 )
  **  (IntArray.seg ret_pre p_pre k l3_2 )
|--
  (EX (l6: (@list Z))  (l5: (@list Z))  (l4: (@list Z))  (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (p_pre <= (i + 1 )) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ ((k + 1 ) = ((p_pre + ((i + 1 ) - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ ((i + 1 ) = (q_pre + 1 )) ”
  &&  (IntArray.seg arr_pre p_pre (i + 1 ) l4 )
  **  (IntArray.seg arr_pre (i + 1 ) (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre (k + 1 ) l3 )
  **  (IntArray.seg ret_pre (k + 1 ) (r_pre + 1 ) l6 ))
  ||
  (EX (l6: (@list Z))  (l5: (@list Z))  (l4: (@list Z))  (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (p_pre <= (i + 1 )) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ ((k + 1 ) = ((p_pre + ((i + 1 ) - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ (j = (r_pre + 1 )) ”
  &&  (IntArray.seg arr_pre p_pre (i + 1 ) l4 )
  **  (IntArray.seg arr_pre (i + 1 ) (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre (k + 1 ) l3 )
  **  (IntArray.seg ret_pre (k + 1 ) (r_pre + 1 ) l6 ))
.

Definition merge_entail_wit_5_1 := 
(
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6_2: (@list Z)) (l5_2: (@list Z)) (l4_2: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (i >= (q_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2_2) (l3_2)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (i = (q_pre + 1 ))) ,
  (IntArray.seg arr_pre p_pre i l4_2 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5_2 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2_2 )
  **  (IntArray.seg ret_pre p_pre k l3_2 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6_2 )
|--
  EX (l6: (@list Z))  (l5: (@list Z))  (l4: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2) (l3)) X ) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ (i = (q_pre + 1 )) ”
  &&  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
) \/
(
forall (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (i >= (q_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2_2) (l3_2)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (i = (q_pre + 1 ))) ,
  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
|--
  “ (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2_2) (l3_2)) X ) ”
  &&  emp
).

Definition merge_entail_wit_5_1_split_goal_1 := 
forall (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (i >= (q_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2_2) (l3_2)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (i = (q_pre + 1 ))) ,
  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
|--
  “ (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2_2) (l3_2)) X ) ”
.

Definition merge_entail_wit_5_1_split_goal_spatial := 
forall (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (i >= (q_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2_2) (l3_2)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (i = (q_pre + 1 ))) ,
  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
|--
  TT && emp 
.

Definition merge_entail_wit_5_2 := 
(
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6_2: (@list Z)) (l5_2: (@list Z)) (l4_2: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (i >= (q_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2_2) (l3_2)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (j = (r_pre + 1 ))) ,
  (IntArray.seg arr_pre p_pre i l4_2 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5_2 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2_2 )
  **  (IntArray.seg ret_pre p_pre k l3_2 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6_2 )
|--
  EX (l6: (@list Z))  (l5: (@list Z))  (l4: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2) (l3)) X ) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ (i = (q_pre + 1 )) ”
  &&  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
) \/
(
forall (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (i >= (q_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2_2) (l3_2)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (j = (r_pre + 1 ))) ,
  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
|--
  “ (i = (q_pre + 1 )) ” 
  &&  “ (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2_2) (l3_2)) X ) ”
  &&  emp
).

Definition merge_entail_wit_5_2_split_goal_1 := 
forall (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (i >= (q_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2_2) (l3_2)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (j = (r_pre + 1 ))) ,
  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
|--
  “ (i = (q_pre + 1 )) ”
.

Definition merge_entail_wit_5_2_split_goal_2 := 
forall (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (i >= (q_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2_2) (l3_2)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (j = (r_pre + 1 ))) ,
  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
|--
  “ (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2_2) (l3_2)) X ) ”
.

Definition merge_entail_wit_5_2_split_goal_spatial := 
forall (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (i >= (q_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2_2) (l3_2)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (j = (r_pre + 1 ))) ,
  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
|--
  TT && emp 
.

Definition merge_entail_wit_6 := 
(
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6_2: (@list Z)) (l5_2: (@list Z)) (l4_2: (@list Z)) (k: Z) (j: Z) (i: Z) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (j < (r_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2_2) (l3_2)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (i = (q_pre + 1 ))) ,
  (IntArray.seg ret_pre k (r_pre + 1 ) (replace_Znth ((k - k )) ((Znth (j - j ) l2_2 0)) (l6_2)) )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2_2 )
  **  (IntArray.seg arr_pre p_pre i l4_2 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5_2 )
  **  (IntArray.seg ret_pre p_pre k l3_2 )
|--
  EX (l6: (@list Z))  (l5: (@list Z))  (l4: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2) (l3)) X ) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= (j + 1 )) ” 
  &&  “ ((k + 1 ) = ((p_pre + (i - p_pre ) ) + ((j + 1 ) - (q_pre + 1 ) ) )) ” 
  &&  “ (i = (q_pre + 1 )) ”
  &&  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) (j + 1 ) l5 )
  **  (IntArray.seg arr_pre (j + 1 ) (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre (k + 1 ) l3 )
  **  (IntArray.seg ret_pre (k + 1 ) (r_pre + 1 ) l6 )
) \/
(
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6_2: (@list Z)) (l5_2: (@list Z)) (k: Z) (j: Z) (i: Z) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (j < (r_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2_2) (l3_2)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (i = (q_pre + 1 ))) ,
  (IntArray.seg ret_pre k (r_pre + 1 ) (replace_Znth ((k - k )) ((Znth (j - j ) l2_2 0)) (l6_2)) )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2_2 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5_2 )
  **  (IntArray.seg ret_pre p_pre k l3_2 )
|--
  EX (l6: (@list Z))  (l5: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2) (l3)) X ) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= (j + 1 )) ” 
  &&  “ ((k + 1 ) = ((p_pre + (i - p_pre ) ) + ((j + 1 ) - (q_pre + 1 ) ) )) ” 
  &&  “ (i = (q_pre + 1 )) ”
  &&  (IntArray.seg arr_pre (q_pre + 1 ) (j + 1 ) l5 )
  **  (IntArray.seg arr_pre (j + 1 ) (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre (k + 1 ) l3 )
  **  (IntArray.seg ret_pre (k + 1 ) (r_pre + 1 ) l6 )
).

Definition merge_return_wit_1 := 
(
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (j >= (r_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2) (l3)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (i = (q_pre + 1 ))) ,
  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  EX (l1: (@list Z))  (s3: (@list Z)) ,
  “ (safeExec ATrue (return (s3)) X ) ”
  &&  (IntArray.seg arr_pre p_pre (r_pre + 1 ) l1 )
  **  (IntArray.seg ret_pre p_pre (r_pre + 1 ) s3 )
) \/
(
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (j >= (r_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2) (l3)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (i = (q_pre + 1 ))) ,
  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  EX (l1: (@list Z))  (s3: (@list Z)) ,
  “ (safeExec ATrue (return (s3)) X ) ”
  &&  (IntArray.seg arr_pre p_pre (r_pre + 1 ) l1 )
  **  (IntArray.seg ret_pre p_pre (r_pre + 1 ) s3 )
).

Definition merge_partial_solve_wit_1 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (j < (r_pre + 1 ))) (PreH2 : (i < (q_pre + 1 ))) (PreH3 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH4 : (p_pre <= i)) (PreH5 : ((q_pre + 1 ) <= j)) (PreH6 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= q_pre)) (PreH9 : (q_pre < r_pre)) (PreH10 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ (j < (r_pre + 1 )) ” 
  &&  “ (i < (q_pre + 1 )) ” 
  &&  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - i ) l1 0))
  **  (IntArray.missing_i arr_pre i i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
.

Definition merge_partial_solve_wit_2 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (j < (r_pre + 1 ))) (PreH2 : (i < (q_pre + 1 ))) (PreH3 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH4 : (p_pre <= i)) (PreH5 : ((q_pre + 1 ) <= j)) (PreH6 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= q_pre)) (PreH9 : (q_pre < r_pre)) (PreH10 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ (j < (r_pre + 1 )) ” 
  &&  “ (i < (q_pre + 1 )) ” 
  &&  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |-> (Znth (j - j ) l2 0))
  **  (IntArray.missing_i arr_pre j j (r_pre + 1 ) l2 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
.

Definition merge_partial_solve_wit_3 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth (i - i ) l1 0) <= (Znth (j - j ) l2 0))) (PreH2 : (j < (r_pre + 1 ))) (PreH3 : (i < (q_pre + 1 ))) (PreH4 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH5 : (p_pre <= i)) (PreH6 : ((q_pre + 1 ) <= j)) (PreH7 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= q_pre)) (PreH10 : (q_pre < r_pre)) (PreH11 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ ((Znth (i - i ) l1 0) <= (Znth (j - j ) l2 0)) ” 
  &&  “ (j < (r_pre + 1 )) ” 
  &&  “ (i < (q_pre + 1 )) ” 
  &&  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - i ) l1 0))
  **  (IntArray.missing_i arr_pre i i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
.

Definition merge_partial_solve_wit_4 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth (i - i ) l1 0) <= (Znth (j - j ) l2 0))) (PreH2 : (j < (r_pre + 1 ))) (PreH3 : (i < (q_pre + 1 ))) (PreH4 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH5 : (p_pre <= i)) (PreH6 : ((q_pre + 1 ) <= j)) (PreH7 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= q_pre)) (PreH10 : (q_pre < r_pre)) (PreH11 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ ((Znth (i - i ) l1 0) <= (Znth (j - j ) l2 0)) ” 
  &&  “ (j < (r_pre + 1 )) ” 
  &&  “ (i < (q_pre + 1 )) ” 
  &&  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ”
  &&  (((ret_pre + (k * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ret_pre k k (r_pre + 1 ) l6 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg ret_pre p_pre k l3 )
.

Definition merge_partial_solve_wit_5 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth (i - i ) l1 0) > (Znth (j - j ) l2 0))) (PreH2 : (j < (r_pre + 1 ))) (PreH3 : (i < (q_pre + 1 ))) (PreH4 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH5 : (p_pre <= i)) (PreH6 : ((q_pre + 1 ) <= j)) (PreH7 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= q_pre)) (PreH10 : (q_pre < r_pre)) (PreH11 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ ((Znth (i - i ) l1 0) > (Znth (j - j ) l2 0)) ” 
  &&  “ (j < (r_pre + 1 )) ” 
  &&  “ (i < (q_pre + 1 )) ” 
  &&  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |-> (Znth (j - j ) l2 0))
  **  (IntArray.missing_i arr_pre j j (r_pre + 1 ) l2 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
.

Definition merge_partial_solve_wit_6 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth (i - i ) l1 0) > (Znth (j - j ) l2 0))) (PreH2 : (j < (r_pre + 1 ))) (PreH3 : (i < (q_pre + 1 ))) (PreH4 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH5 : (p_pre <= i)) (PreH6 : ((q_pre + 1 ) <= j)) (PreH7 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= q_pre)) (PreH10 : (q_pre < r_pre)) (PreH11 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ ((Znth (i - i ) l1 0) > (Znth (j - j ) l2 0)) ” 
  &&  “ (j < (r_pre + 1 )) ” 
  &&  “ (i < (q_pre + 1 )) ” 
  &&  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ”
  &&  (((ret_pre + (k * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ret_pre k k (r_pre + 1 ) l6 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg ret_pre p_pre k l3 )
.

Definition merge_partial_solve_wit_7 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (i < (q_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (j = (r_pre + 1 ))) ,
  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ (i < (q_pre + 1 )) ” 
  &&  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ (j = (r_pre + 1 )) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - i ) l1 0))
  **  (IntArray.missing_i arr_pre i i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
.

Definition merge_partial_solve_wit_8 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (i < (q_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (j = (r_pre + 1 ))) ,
  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ (i < (q_pre + 1 )) ” 
  &&  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ (j = (r_pre + 1 )) ”
  &&  (((ret_pre + (k * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ret_pre k k (r_pre + 1 ) l6 )
  **  (IntArray.seg arr_pre i (q_pre + 1 ) l1 )
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
.

Definition merge_partial_solve_wit_9 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (j < (r_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2) (l3)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (i = (q_pre + 1 ))) ,
  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ (j < (r_pre + 1 )) ” 
  &&  “ (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2) (l3)) X ) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ (i = (q_pre + 1 )) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |-> (Znth (j - j ) l2 0))
  **  (IntArray.missing_i arr_pre j j (r_pre + 1 ) l2 )
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
.

Definition merge_partial_solve_wit_10 := 
forall (ret_pre: Z) (r_pre: Z) (q_pre: Z) (p_pre: Z) (arr_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (l6: (@list Z)) (l5: (@list Z)) (l4: (@list Z)) (k: Z) (j: Z) (i: Z) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (j < (r_pre + 1 ))) (PreH2 : (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2) (l3)) X )) (PreH3 : (0 <= p_pre)) (PreH4 : (p_pre <= q_pre)) (PreH5 : (q_pre < r_pre)) (PreH6 : ((r_pre + 1 ) <= INT_MAX)) (PreH7 : (p_pre <= i)) (PreH8 : ((q_pre + 1 ) <= j)) (PreH9 : (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) ))) (PreH10 : (i = (q_pre + 1 ))) ,
  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg ret_pre p_pre k l3 )
  **  (IntArray.seg ret_pre k (r_pre + 1 ) l6 )
|--
  “ (j < (r_pre + 1 )) ” 
  &&  “ (safeExec ATrue (merge_from_mid_rel ((@nil Z)) (l2) (l3)) X ) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= q_pre) ” 
  &&  “ (q_pre < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (p_pre <= i) ” 
  &&  “ ((q_pre + 1 ) <= j) ” 
  &&  “ (k = ((p_pre + (i - p_pre ) ) + (j - (q_pre + 1 ) ) )) ” 
  &&  “ (i = (q_pre + 1 )) ”
  &&  (((ret_pre + (k * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ret_pre k k (r_pre + 1 ) l6 )
  **  (IntArray.seg arr_pre j (r_pre + 1 ) l2 )
  **  (IntArray.seg arr_pre p_pre i l4 )
  **  (IntArray.seg arr_pre (q_pre + 1 ) j l5 )
  **  (IntArray.seg ret_pre p_pre k l3 )
.

(*----- Function mergeSort -----*)

Definition mergeSort_safety_wit_1 := 
(
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (s1_low_level_spec: (@list Z)) (PreH1 : (l_pre < r_pre)) (PreH2 : (safeExec ATrue (gmergesortrec (s1_low_level_spec)) X_low_level_spec )) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) ,
  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.seg arr_pre l_pre (r_pre + 1 ) s1_low_level_spec )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) s1_low_level_spec )
|--
  “ ((l_pre + ((r_pre - l_pre ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (l_pre + ((r_pre - l_pre ) ÷ 2 ) )) ”
) \/
(
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (s1_low_level_spec: (@list Z)) (PreH1 : (l_pre < r_pre)) (PreH2 : (safeExec ATrue (gmergesortrec (s1_low_level_spec)) X_low_level_spec )) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) ,
  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.seg arr_pre l_pre (r_pre + 1 ) s1_low_level_spec )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) s1_low_level_spec )
|--
  “ ((l_pre + ((r_pre - l_pre ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (l_pre + ((r_pre - l_pre ) ÷ 2 ) )) ”
).

Definition mergeSort_safety_wit_1_split_goal_1 := 
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (s1_low_level_spec: (@list Z)) (PreH1 : (l_pre < r_pre)) (PreH2 : (safeExec ATrue (gmergesortrec (s1_low_level_spec)) X_low_level_spec )) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) ,
  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.seg arr_pre l_pre (r_pre + 1 ) s1_low_level_spec )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) s1_low_level_spec )
|--
  “ ((l_pre + ((r_pre - l_pre ) ÷ 2 ) ) <= INT_MAX) ”
.

Definition mergeSort_safety_wit_1_split_goal_2 := 
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (s1_low_level_spec: (@list Z)) (PreH1 : (l_pre < r_pre)) (PreH2 : (safeExec ATrue (gmergesortrec (s1_low_level_spec)) X_low_level_spec )) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) ,
  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.seg arr_pre l_pre (r_pre + 1 ) s1_low_level_spec )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) s1_low_level_spec )
|--
  “ ((INT_MIN) <= (l_pre + ((r_pre - l_pre ) ÷ 2 ) )) ”
.

Definition mergeSort_safety_wit_2 := 
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (s1_low_level_spec: (@list Z)) (PreH1 : (l_pre < r_pre)) (PreH2 : (safeExec ATrue (gmergesortrec (s1_low_level_spec)) X_low_level_spec )) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) ,
  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.seg arr_pre l_pre (r_pre + 1 ) s1_low_level_spec )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) s1_low_level_spec )
|--
  “ (((r_pre - l_pre ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition mergeSort_safety_wit_3 := 
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (s1_low_level_spec: (@list Z)) (PreH1 : (l_pre < r_pre)) (PreH2 : (safeExec ATrue (gmergesortrec (s1_low_level_spec)) X_low_level_spec )) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) ,
  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.seg arr_pre l_pre (r_pre + 1 ) s1_low_level_spec )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) s1_low_level_spec )
|--
  “ ((r_pre - l_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r_pre - l_pre )) ”
.

Definition mergeSort_safety_wit_4 := 
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (s1_low_level_spec: (@list Z)) (PreH1 : (l_pre < r_pre)) (PreH2 : (safeExec ATrue (gmergesortrec (s1_low_level_spec)) X_low_level_spec )) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) ,
  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.seg arr_pre l_pre (r_pre + 1 ) s1_low_level_spec )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) s1_low_level_spec )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mergeSort_safety_wit_5 := 
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (m: Z) (l3: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec )) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : ((r_pre + 1 ) <= INT_MAX)) (PreH5 : (l_pre < r_pre)) (PreH6 : (l_pre <= m)) (PreH7 : (m < r_pre)) ,
  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.seg arr_pre l_pre (m + 1 ) l1 )
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  (IntArray.seg arr_pre (m + 1 ) (r_pre + 1 ) l2 )
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  (IntArray.seg ret_pre l_pre (m + 1 ) l3 )
  **  (IntArray.seg ret_pre (m + 1 ) (r_pre + 1 ) l2 )
|--
  “ ((m + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (m + 1 )) ”
.

Definition mergeSort_safety_wit_6 := 
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (m: Z) (l3: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec )) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : ((r_pre + 1 ) <= INT_MAX)) (PreH5 : (l_pre < r_pre)) (PreH6 : (l_pre <= m)) (PreH7 : (m < r_pre)) ,
  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.seg arr_pre l_pre (m + 1 ) l1 )
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  (IntArray.seg arr_pre (m + 1 ) (r_pre + 1 ) l2 )
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  (IntArray.seg ret_pre l_pre (m + 1 ) l3 )
  **  (IntArray.seg ret_pre (m + 1 ) (r_pre + 1 ) l2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mergeSort_entail_wit_1 := 
(
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (s1_low_level_spec: (@list Z)) (PreH1 : (l_pre < r_pre)) (PreH2 : (safeExec ATrue (gmergesortrec (s1_low_level_spec)) X_low_level_spec )) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg arr_pre l_pre (r_pre + 1 ) s1_low_level_spec )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) s1_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec ) ” 
  &&  “ (0 <= l_pre) ” 
  &&  “ (l_pre <= r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (l_pre < r_pre) ” 
  &&  “ (l_pre <= (l_pre + ((r_pre - l_pre ) ÷ 2 ) )) ” 
  &&  “ ((l_pre + ((r_pre - l_pre ) ÷ 2 ) ) < r_pre) ”
  &&  (IntArray.seg arr_pre l_pre ((l_pre + ((r_pre - l_pre ) ÷ 2 ) ) + 1 ) l1 )
  **  (IntArray.seg arr_pre ((l_pre + ((r_pre - l_pre ) ÷ 2 ) ) + 1 ) (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre l_pre ((l_pre + ((r_pre - l_pre ) ÷ 2 ) ) + 1 ) l1 )
  **  (IntArray.seg ret_pre ((l_pre + ((r_pre - l_pre ) ÷ 2 ) ) + 1 ) (r_pre + 1 ) l2 )
) \/
(
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (s1_low_level_spec: (@list Z)) (PreH1 : (l_pre < r_pre)) (PreH2 : (safeExec ATrue (gmergesortrec (s1_low_level_spec)) X_low_level_spec )) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg arr_pre l_pre (r_pre + 1 ) s1_low_level_spec )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) s1_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec ) ” 
  &&  “ (0 <= l_pre) ” 
  &&  “ (l_pre <= r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (l_pre < r_pre) ” 
  &&  “ (l_pre <= (l_pre + ((r_pre - l_pre ) ÷ 2 ) )) ” 
  &&  “ ((l_pre + ((r_pre - l_pre ) ÷ 2 ) ) < r_pre) ”
  &&  (IntArray.seg arr_pre l_pre ((l_pre + ((r_pre - l_pre ) ÷ 2 ) ) + 1 ) l1 )
  **  (IntArray.seg arr_pre ((l_pre + ((r_pre - l_pre ) ÷ 2 ) ) + 1 ) (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre l_pre ((l_pre + ((r_pre - l_pre ) ÷ 2 ) ) + 1 ) l1 )
  **  (IntArray.seg ret_pre ((l_pre + ((r_pre - l_pre ) ÷ 2 ) ) + 1 ) (r_pre + 1 ) l2 )
).

Definition mergeSort_entail_wit_2 := 
(
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l2_2: (@list Z)) (m: Z) (l2_3: (@list Z)) (l1_2: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((gmergesortrec_loc1 (l2_2))) (l1_2)) X_low_level_spec )) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : ((r_pre + 1 ) <= INT_MAX)) (PreH5 : (l_pre < r_pre)) (PreH6 : (l_pre <= m)) (PreH7 : (m < r_pre)) ,
  (IntArray.seg ret_pre l_pre (m + 1 ) l2_3 )
  **  (IntArray.seg arr_pre l_pre (m + 1 ) l1_2 )
  **  (IntArray.seg arr_pre (m + 1 ) (r_pre + 1 ) l2_2 )
  **  (IntArray.seg ret_pre (m + 1 ) (r_pre + 1 ) l2_2 )
|--
  EX (l3: (@list Z))  (l2: (@list Z))  (l1: (@list Z)) ,
  “ (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ” 
  &&  “ (0 <= l_pre) ” 
  &&  “ (l_pre <= r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (l_pre < r_pre) ” 
  &&  “ (l_pre <= m) ” 
  &&  “ (m < r_pre) ”
  &&  (IntArray.seg arr_pre l_pre (m + 1 ) l1 )
  **  (IntArray.seg arr_pre (m + 1 ) (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre l_pre (m + 1 ) l3 )
  **  (IntArray.seg ret_pre (m + 1 ) (r_pre + 1 ) l2 )
) \/
(
forall (r_pre: Z) (l_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l2_2: (@list Z)) (m: Z) (l1_2: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((gmergesortrec_loc1 (l2_2))) (l1_2)) X_low_level_spec )) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : ((r_pre + 1 ) <= INT_MAX)) (PreH5 : (l_pre < r_pre)) (PreH6 : (l_pre <= m)) (PreH7 : (m < r_pre)) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((gmergesortrec (l2_2))) ((mergesortrec_loc2 (l1_2)))) X_low_level_spec ) ”
  &&  emp
).

Definition mergeSort_entail_wit_2_split_goal_1 := 
forall (r_pre: Z) (l_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l2_2: (@list Z)) (m: Z) (l1_2: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((gmergesortrec_loc1 (l2_2))) (l1_2)) X_low_level_spec )) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : ((r_pre + 1 ) <= INT_MAX)) (PreH5 : (l_pre < r_pre)) (PreH6 : (l_pre <= m)) (PreH7 : (m < r_pre)) ,
  (safeExec ATrue (bind ((gmergesortrec (l2_2))) ((mergesortrec_loc2 (l1_2)))) X_low_level_spec )
.

Definition mergeSort_entail_wit_3 := 
(
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (m: Z) (l3: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (l1_2: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc2 (l1))) (l1_2)) X_low_level_spec )) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : ((r_pre + 1 ) <= INT_MAX)) (PreH5 : (l_pre < r_pre)) (PreH6 : (l_pre <= m)) (PreH7 : (m < r_pre)) ,
  (IntArray.seg ret_pre (m + 1 ) (r_pre + 1 ) l2 )
  **  (IntArray.seg arr_pre (m + 1 ) (r_pre + 1 ) l1_2 )
  **  (IntArray.seg arr_pre l_pre (m + 1 ) l1 )
  **  (IntArray.seg ret_pre l_pre (m + 1 ) l3 )
|--
  EX (l0: (@list Z))  (s1: (@list Z))  (s2: (@list Z)) ,
  “ (safeExec ATrue (merge_rel (s1) (s2)) X_low_level_spec ) ” 
  &&  “ (0 <= l_pre) ” 
  &&  “ (l_pre <= r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (l_pre < r_pre) ” 
  &&  “ (l_pre <= m) ” 
  &&  “ (m < r_pre) ”
  &&  (IntArray.seg arr_pre l_pre (m + 1 ) s1 )
  **  (IntArray.seg arr_pre (m + 1 ) (r_pre + 1 ) s2 )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) l0 )
) \/
(
forall (r_pre: Z) (l_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (m: Z) (l1: (@list Z)) (l1_2: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc2 (l1))) (l1_2)) X_low_level_spec )) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : ((r_pre + 1 ) <= INT_MAX)) (PreH5 : (l_pre < r_pre)) (PreH6 : (l_pre <= m)) (PreH7 : (m < r_pre)) ,
  TT && emp 
|--
  “ (safeExec ATrue (merge_rel (l1) (l1_2)) X_low_level_spec ) ”
  &&  emp
).

Definition mergeSort_entail_wit_3_split_goal_1 := 
forall (r_pre: Z) (l_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (m: Z) (l1: (@list Z)) (l1_2: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc2 (l1))) (l1_2)) X_low_level_spec )) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : ((r_pre + 1 ) <= INT_MAX)) (PreH5 : (l_pre < r_pre)) (PreH6 : (l_pre <= m)) (PreH7 : (m < r_pre)) ,
  (safeExec ATrue (merge_rel (l1) (l1_2)) X_low_level_spec )
.

Definition mergeSort_return_wit_1 := 
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (m: Z) (l1: (@list Z)) (s3_2: (@list Z)) (PreH1 : (safeExec ATrue (return (s3_2)) X_low_level_spec )) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : ((r_pre + 1 ) <= INT_MAX)) (PreH5 : (l_pre < r_pre)) (PreH6 : (l_pre <= m)) (PreH7 : (m < r_pre)) ,
  (IntArray.seg arr_pre l_pre (r_pre + 1 ) l1 )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) s3_2 )
|--
  EX (s3: (@list Z))  (s2: (@list Z)) ,
  “ (safeExec ATrue (return (s2)) X_low_level_spec ) ”
  &&  (IntArray.seg arr_pre l_pre (r_pre + 1 ) s3 )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) s2 )
.

Definition mergeSort_return_wit_2 := 
(
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (s1_low_level_spec: (@list Z)) (PreH1 : (l_pre >= r_pre)) (PreH2 : (safeExec ATrue (gmergesortrec (s1_low_level_spec)) X_low_level_spec )) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) ,
  (IntArray.seg arr_pre l_pre (r_pre + 1 ) s1_low_level_spec )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) s1_low_level_spec )
|--
  EX (s3: (@list Z))  (s2: (@list Z)) ,
  “ (safeExec ATrue (return (s2)) X_low_level_spec ) ”
  &&  (IntArray.seg arr_pre l_pre (r_pre + 1 ) s3 )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) s2 )
) \/
(
forall (r_pre: Z) (l_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (s1_low_level_spec: (@list Z)) (PreH1 : (l_pre >= r_pre)) (PreH2 : (safeExec ATrue (gmergesortrec (s1_low_level_spec)) X_low_level_spec )) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) ,
  TT && emp 
|--
  “ (safeExec ATrue (return (s1_low_level_spec)) X_low_level_spec ) ”
  &&  emp
).

Definition mergeSort_return_wit_2_split_goal_1 := 
forall (r_pre: Z) (l_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (s1_low_level_spec: (@list Z)) (PreH1 : (l_pre >= r_pre)) (PreH2 : (safeExec ATrue (gmergesortrec (s1_low_level_spec)) X_low_level_spec )) (PreH3 : (0 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : ((r_pre + 1 ) <= INT_MAX)) ,
  (safeExec ATrue (return (s1_low_level_spec)) X_low_level_spec )
.

Definition mergeSort_partial_solve_wit_1_pure := 
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (m: Z) (PreH1 : (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec )) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : ((r_pre + 1 ) <= INT_MAX)) (PreH5 : (l_pre < r_pre)) (PreH6 : (l_pre <= m)) (PreH7 : (m < r_pre)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  (IntArray.seg arr_pre l_pre (m + 1 ) l1 )
  **  (IntArray.seg arr_pre (m + 1 ) (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre l_pre (m + 1 ) l1 )
  **  (IntArray.seg ret_pre (m + 1 ) (r_pre + 1 ) l2 )
|--
  “ (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec ) ” 
  &&  “ (0 <= l_pre) ” 
  &&  “ (l_pre <= m) ” 
  &&  “ ((m + 1 ) <= INT_MAX) ”
.

Definition mergeSort_partial_solve_wit_1_aux := 
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (m: Z) (PreH1 : (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec )) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : ((r_pre + 1 ) <= INT_MAX)) (PreH5 : (l_pre < r_pre)) (PreH6 : (l_pre <= m)) (PreH7 : (m < r_pre)) ,
  (IntArray.seg arr_pre l_pre (m + 1 ) l1 )
  **  (IntArray.seg arr_pre (m + 1 ) (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre l_pre (m + 1 ) l1 )
  **  (IntArray.seg ret_pre (m + 1 ) (r_pre + 1 ) l2 )
|--
  “ (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec ) ” 
  &&  “ (0 <= l_pre) ” 
  &&  “ (l_pre <= m) ” 
  &&  “ ((m + 1 ) <= INT_MAX) ” 
  &&  “ (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec ) ” 
  &&  “ (0 <= l_pre) ” 
  &&  “ (l_pre <= r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (l_pre < r_pre) ” 
  &&  “ (l_pre <= m) ” 
  &&  “ (m < r_pre) ”
  &&  (IntArray.seg ret_pre l_pre (m + 1 ) l1 )
  **  (IntArray.seg arr_pre l_pre (m + 1 ) l1 )
  **  (IntArray.seg arr_pre (m + 1 ) (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre (m + 1 ) (r_pre + 1 ) l2 )
.

Definition mergeSort_partial_solve_wit_1 := mergeSort_partial_solve_wit_1_pure -> mergeSort_partial_solve_wit_1_aux.

Definition mergeSort_partial_solve_wit_2_pure := 
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (m: Z) (l3: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec )) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : ((r_pre + 1 ) <= INT_MAX)) (PreH5 : (l_pre < r_pre)) (PreH6 : (l_pre <= m)) (PreH7 : (m < r_pre)) ,
  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.seg arr_pre l_pre (m + 1 ) l1 )
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  (IntArray.seg arr_pre (m + 1 ) (r_pre + 1 ) l2 )
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  (IntArray.seg ret_pre l_pre (m + 1 ) l3 )
  **  (IntArray.seg ret_pre (m + 1 ) (r_pre + 1 ) l2 )
|--
  “ (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ” 
  &&  “ (0 <= (m + 1 )) ” 
  &&  “ ((m + 1 ) <= r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ”
.

Definition mergeSort_partial_solve_wit_2_aux := 
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (m: Z) (l3: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec )) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : ((r_pre + 1 ) <= INT_MAX)) (PreH5 : (l_pre < r_pre)) (PreH6 : (l_pre <= m)) (PreH7 : (m < r_pre)) ,
  (IntArray.seg arr_pre l_pre (m + 1 ) l1 )
  **  (IntArray.seg arr_pre (m + 1 ) (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre l_pre (m + 1 ) l3 )
  **  (IntArray.seg ret_pre (m + 1 ) (r_pre + 1 ) l2 )
|--
  “ (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ” 
  &&  “ (0 <= (m + 1 )) ” 
  &&  “ ((m + 1 ) <= r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ” 
  &&  “ (0 <= l_pre) ” 
  &&  “ (l_pre <= r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (l_pre < r_pre) ” 
  &&  “ (l_pre <= m) ” 
  &&  “ (m < r_pre) ”
  &&  (IntArray.seg ret_pre (m + 1 ) (r_pre + 1 ) l2 )
  **  (IntArray.seg arr_pre (m + 1 ) (r_pre + 1 ) l2 )
  **  (IntArray.seg arr_pre l_pre (m + 1 ) l1 )
  **  (IntArray.seg ret_pre l_pre (m + 1 ) l3 )
.

Definition mergeSort_partial_solve_wit_2 := mergeSort_partial_solve_wit_2_pure -> mergeSort_partial_solve_wit_2_aux.

Definition mergeSort_partial_solve_wit_3_pure := 
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (m: Z) (l0: (@list Z)) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (safeExec ATrue (merge_rel (s1) (s2)) X_low_level_spec )) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : ((r_pre + 1 ) <= INT_MAX)) (PreH5 : (l_pre < r_pre)) (PreH6 : (l_pre <= m)) (PreH7 : (m < r_pre)) ,
  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "l" ) )) # Int  |-> l_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.seg arr_pre l_pre (m + 1 ) s1 )
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  (IntArray.seg arr_pre (m + 1 ) (r_pre + 1 ) s2 )
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) l0 )
|--
  “ (safeExec ATrue (merge_rel (s1) (s2)) X_low_level_spec ) ” 
  &&  “ (0 <= l_pre) ” 
  &&  “ (l_pre <= m) ” 
  &&  “ (m < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ”
.

Definition mergeSort_partial_solve_wit_3_aux := 
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (m: Z) (l0: (@list Z)) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (safeExec ATrue (merge_rel (s1) (s2)) X_low_level_spec )) (PreH2 : (0 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : ((r_pre + 1 ) <= INT_MAX)) (PreH5 : (l_pre < r_pre)) (PreH6 : (l_pre <= m)) (PreH7 : (m < r_pre)) ,
  (IntArray.seg arr_pre l_pre (m + 1 ) s1 )
  **  (IntArray.seg arr_pre (m + 1 ) (r_pre + 1 ) s2 )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) l0 )
|--
  “ (safeExec ATrue (merge_rel (s1) (s2)) X_low_level_spec ) ” 
  &&  “ (0 <= l_pre) ” 
  &&  “ (l_pre <= m) ” 
  &&  “ (m < r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (safeExec ATrue (merge_rel (s1) (s2)) X_low_level_spec ) ” 
  &&  “ (0 <= l_pre) ” 
  &&  “ (l_pre <= r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ” 
  &&  “ (l_pre < r_pre) ” 
  &&  “ (l_pre <= m) ” 
  &&  “ (m < r_pre) ”
  &&  (IntArray.seg arr_pre l_pre (m + 1 ) s1 )
  **  (IntArray.seg arr_pre (m + 1 ) (r_pre + 1 ) s2 )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) l0 )
.

Definition mergeSort_partial_solve_wit_3 := mergeSort_partial_solve_wit_3_pure -> mergeSort_partial_solve_wit_3_aux.

Definition mergeSort_derive_low_level_spec_aux_by_low_level_spec := 
forall (B: Type) ,
forall (ret_pre: Z) (r_pre: Z) (l_pre: Z) (arr_pre: Z) (X_low_level_spec_aux: (B -> (unit -> Prop))) (c_low_level_spec_aux: ((@list Z) -> (@ StateRelMonad.M  unit B))) (l0_low_level_spec_aux: (@list Z)) ,
  “ (safeExec ATrue (bind ((gmergesortrec (l0_low_level_spec_aux))) (c_low_level_spec_aux)) X_low_level_spec_aux ) ” 
  &&  “ (0 <= l_pre) ” 
  &&  “ (l_pre <= r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ”
  &&  (IntArray.seg arr_pre l_pre (r_pre + 1 ) l0_low_level_spec_aux )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) l0_low_level_spec_aux )
|--
EX (s1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) ,
  (“ (safeExec ATrue (gmergesortrec (s1_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (0 <= l_pre) ” 
  &&  “ (l_pre <= r_pre) ” 
  &&  “ ((r_pre + 1 ) <= INT_MAX) ”
  &&  (IntArray.seg arr_pre l_pre (r_pre + 1 ) s1_low_level_spec )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) s1_low_level_spec ))
  **
  ((EX s3 s2,
  “ (safeExec ATrue (return (s2)) X_low_level_spec ) ”
  &&  (IntArray.seg arr_pre l_pre (r_pre + 1 ) s3 )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) s2 ))
  -*
  (EX l2 l1,
  “ (safeExec ATrue (applyf (c_low_level_spec_aux) (l1)) X_low_level_spec_aux ) ”
  &&  (IntArray.seg arr_pre l_pre (r_pre + 1 ) l2 )
  **  (IntArray.seg ret_pre l_pre (r_pre + 1 ) l1 )))
.

Module Type VC_Correct.

Include safeexec_Strategy_Correct.

Axiom proof_of_merge_safety_wit_1 : merge_safety_wit_1.
Axiom proof_of_merge_safety_wit_2 : merge_safety_wit_2.
Axiom proof_of_merge_safety_wit_3 : merge_safety_wit_3.
Axiom proof_of_merge_safety_wit_4 : merge_safety_wit_4.
Axiom proof_of_merge_safety_wit_5 : merge_safety_wit_5.
Axiom proof_of_merge_safety_wit_6 : merge_safety_wit_6.
Axiom proof_of_merge_safety_wit_7 : merge_safety_wit_7.
Axiom proof_of_merge_safety_wit_8 : merge_safety_wit_8.
Axiom proof_of_merge_safety_wit_9 : merge_safety_wit_9.
Axiom proof_of_merge_safety_wit_10 : merge_safety_wit_10.
Axiom proof_of_merge_safety_wit_11 : merge_safety_wit_11.
Axiom proof_of_merge_safety_wit_12 : merge_safety_wit_12.
Axiom proof_of_merge_safety_wit_13 : merge_safety_wit_13.
Axiom proof_of_merge_safety_wit_14 : merge_safety_wit_14.
Axiom proof_of_merge_safety_wit_15 : merge_safety_wit_15.
Axiom proof_of_merge_safety_wit_16 : merge_safety_wit_16.
Axiom proof_of_merge_safety_wit_17 : merge_safety_wit_17.
Axiom proof_of_merge_safety_wit_18 : merge_safety_wit_18.
Axiom proof_of_merge_safety_wit_19 : merge_safety_wit_19.
Axiom proof_of_merge_safety_wit_20 : merge_safety_wit_20.
Axiom proof_of_merge_safety_wit_21 : merge_safety_wit_21.
Axiom proof_of_merge_entail_wit_1 : merge_entail_wit_1.
Axiom proof_of_merge_entail_wit_2_1 : merge_entail_wit_2_1.
Axiom proof_of_merge_entail_wit_2_2 : merge_entail_wit_2_2.
Axiom proof_of_merge_entail_wit_3_1 : merge_entail_wit_3_1.
Axiom proof_of_merge_entail_wit_3_2 : merge_entail_wit_3_2.
Axiom proof_of_merge_entail_wit_4 : merge_entail_wit_4.
Axiom proof_of_merge_entail_wit_5_1 : merge_entail_wit_5_1.
Axiom proof_of_merge_entail_wit_5_2 : merge_entail_wit_5_2.
Axiom proof_of_merge_entail_wit_6 : merge_entail_wit_6.
Axiom proof_of_merge_return_wit_1 : merge_return_wit_1.
Axiom proof_of_merge_partial_solve_wit_1 : merge_partial_solve_wit_1.
Axiom proof_of_merge_partial_solve_wit_2 : merge_partial_solve_wit_2.
Axiom proof_of_merge_partial_solve_wit_3 : merge_partial_solve_wit_3.
Axiom proof_of_merge_partial_solve_wit_4 : merge_partial_solve_wit_4.
Axiom proof_of_merge_partial_solve_wit_5 : merge_partial_solve_wit_5.
Axiom proof_of_merge_partial_solve_wit_6 : merge_partial_solve_wit_6.
Axiom proof_of_merge_partial_solve_wit_7 : merge_partial_solve_wit_7.
Axiom proof_of_merge_partial_solve_wit_8 : merge_partial_solve_wit_8.
Axiom proof_of_merge_partial_solve_wit_9 : merge_partial_solve_wit_9.
Axiom proof_of_merge_partial_solve_wit_10 : merge_partial_solve_wit_10.
Axiom proof_of_mergeSort_safety_wit_1 : mergeSort_safety_wit_1.
Axiom proof_of_mergeSort_safety_wit_2 : mergeSort_safety_wit_2.
Axiom proof_of_mergeSort_safety_wit_3 : mergeSort_safety_wit_3.
Axiom proof_of_mergeSort_safety_wit_4 : mergeSort_safety_wit_4.
Axiom proof_of_mergeSort_safety_wit_5 : mergeSort_safety_wit_5.
Axiom proof_of_mergeSort_safety_wit_6 : mergeSort_safety_wit_6.
Axiom proof_of_mergeSort_entail_wit_1 : mergeSort_entail_wit_1.
Axiom proof_of_mergeSort_entail_wit_2 : mergeSort_entail_wit_2.
Axiom proof_of_mergeSort_entail_wit_3 : mergeSort_entail_wit_3.
Axiom proof_of_mergeSort_return_wit_1 : mergeSort_return_wit_1.
Axiom proof_of_mergeSort_return_wit_2 : mergeSort_return_wit_2.
Axiom proof_of_mergeSort_partial_solve_wit_1_pure : mergeSort_partial_solve_wit_1_pure.
Axiom proof_of_mergeSort_partial_solve_wit_1 : mergeSort_partial_solve_wit_1.
Axiom proof_of_mergeSort_partial_solve_wit_2_pure : mergeSort_partial_solve_wit_2_pure.
Axiom proof_of_mergeSort_partial_solve_wit_2 : mergeSort_partial_solve_wit_2.
Axiom proof_of_mergeSort_partial_solve_wit_3_pure : mergeSort_partial_solve_wit_3_pure.
Axiom proof_of_mergeSort_partial_solve_wit_3 : mergeSort_partial_solve_wit_3.
Axiom proof_of_mergeSort_derive_low_level_spec_aux_by_low_level_spec : mergeSort_derive_low_level_spec_aux_by_low_level_spec.

End VC_Correct.
