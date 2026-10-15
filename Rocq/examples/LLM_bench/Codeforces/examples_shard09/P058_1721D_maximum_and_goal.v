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
Require Import AUXLib.MonotonicList.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P058_1721D_maximum_and_lib.
Local Open Scope sac.

(*----- Function feasible -----*)

Definition feasible_safety_wit_1 := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (left)))) (PreH4 : ((Zlength (right)) = n_pre)) (PreH5 : (0 <= mask_pre)) (PreH6 : (mask_pre < 1073741824)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i left 0)) /\ ((Znth i left 0) < 1073741824)))) (PreH8 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) < 1073741824)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mask" ) )) # UInt  |-> mask_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_2 := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_next: (@list Z)) (kb_next: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (left)))) (PreH4 : ((Zlength (right)) = n_pre)) (PreH5 : (0 <= mask_pre)) (PreH6 : (mask_pre < 1073741824)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (MaskedBuffersPrefix left right mask_pre ka_next kb_next (i + 1 ) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mask" ) )) # UInt  |-> mask_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.seg ka_pre 0 (i + 1 ) ka_next )
  **  (UIntArray.undef_seg ka_pre (i + 1 ) n_pre )
  **  (UIntArray.seg kb_pre 0 (i + 1 ) kb_next )
  **  (UIntArray.undef_seg kb_pre (i + 1 ) n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition feasible_safety_wit_3 := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (sorted_ka: (@list Z)) (sorted_kb: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (left)))) (PreH4 : ((Zlength (right)) = n_pre)) (PreH5 : (0 <= mask_pre)) (PreH6 : (mask_pre < 1073741824)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH9 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre )) (PreH10 : (Permutation ka_values sorted_ka )) (PreH11 : (Permutation kb_values sorted_kb )) (PreH12 : (mono_nondec sorted_ka )) (PreH13 : (mono_nondec sorted_kb )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mask" ) )) # UInt  |-> mask_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full ka_pre n_pre sorted_ka )
  **  (UIntArray.full kb_pre n_pre sorted_kb )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_4 := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (sorted_kb: (@list Z)) (sorted_ka: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : ((Znth i sorted_ka 0) <> (Znth i sorted_kb 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : ((Zlength (right)) = n_pre)) (PreH7 : (0 <= mask_pre)) (PreH8 : (mask_pre < 1073741824)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH10 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre )) (PreH14 : (Permutation ka_values sorted_ka )) (PreH15 : (Permutation kb_values sorted_kb )) (PreH16 : (mono_nondec sorted_ka )) (PreH17 : (mono_nondec sorted_kb )) (PreH18 : ((sublist (0) (i) (sorted_ka)) = (sublist (0) (i) (sorted_kb)))) ,
  (UIntArray.full kb_pre n_pre sorted_kb )
  **  (UIntArray.full ka_pre n_pre sorted_ka )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mask" ) )) # UInt  |-> mask_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_5 := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (sorted_kb: (@list Z)) (sorted_ka: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : (0 <= mask_pre)) (PreH7 : (mask_pre < 1073741824)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre )) (PreH13 : (Permutation ka_values sorted_ka )) (PreH14 : (Permutation kb_values sorted_kb )) (PreH15 : (mono_nondec sorted_ka )) (PreH16 : (mono_nondec sorted_kb )) (PreH17 : ((sublist (0) (i) (sorted_ka)) = (sublist (0) (i) (sorted_kb)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mask" ) )) # UInt  |-> mask_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full ka_pre n_pre sorted_ka )
  **  (UIntArray.full kb_pre n_pre sorted_kb )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition feasible_safety_wit_6 := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (sorted_kb: (@list Z)) (sorted_ka: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : ((Znth i sorted_ka 0) = (Znth i sorted_kb 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : ((Zlength (right)) = n_pre)) (PreH7 : (0 <= mask_pre)) (PreH8 : (mask_pre < 1073741824)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH10 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre )) (PreH14 : (Permutation ka_values sorted_ka )) (PreH15 : (Permutation kb_values sorted_kb )) (PreH16 : (mono_nondec sorted_ka )) (PreH17 : (mono_nondec sorted_kb )) (PreH18 : ((sublist (0) (i) (sorted_ka)) = (sublist (0) (i) (sorted_kb)))) ,
  (UIntArray.full kb_pre n_pre sorted_kb )
  **  (UIntArray.full ka_pre n_pre sorted_ka )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mask" ) )) # UInt  |-> mask_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition feasible_entail_wit_1 := 
(
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (left)))) (PreH4 : ((Zlength (right)) = n_pre)) (PreH5 : (0 <= mask_pre)) (PreH6 : (mask_pre < 1073741824)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i left 0)) /\ ((Znth i left 0) < 1073741824)))) (PreH8 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) < 1073741824)))) ,
  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre )
|--
  EX (ka_values: (@list Z))  (kb_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ (0 <= mask_pre) ” 
  &&  “ (mask_pre < 1073741824) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (MaskedBuffersPrefix left right mask_pre ka_values kb_values 0 ) ”
  &&  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.seg ka_pre 0 0 ka_values )
  **  (UIntArray.undef_seg ka_pre 0 n_pre )
  **  (UIntArray.seg kb_pre 0 0 kb_values )
  **  (UIntArray.undef_seg kb_pre 0 n_pre )
) \/
(
forall (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (left)))) (PreH4 : ((Zlength (right)) = n_pre)) (PreH5 : (0 <= mask_pre)) (PreH6 : (mask_pre < 1073741824)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i left 0)) /\ ((Znth i left 0) < 1073741824)))) (PreH8 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) < 1073741824)))) ,
  TT && emp 
|--
  “ (MaskedBuffersPrefix left right mask_pre (@nil Z) (@nil Z) 0 ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ”
  &&  emp
).

Definition feasible_entail_wit_1_split_goal_1 := 
forall (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (left)))) (PreH4 : ((Zlength (right)) = n_pre)) (PreH5 : (0 <= mask_pre)) (PreH6 : (mask_pre < 1073741824)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i left 0)) /\ ((Znth i left 0) < 1073741824)))) (PreH8 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) < 1073741824)))) ,
  (MaskedBuffersPrefix left right mask_pre (@nil Z) (@nil Z) 0 )
.

Definition feasible_entail_wit_1_split_goal_2 := 
forall (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (left)))) (PreH4 : ((Zlength (right)) = n_pre)) (PreH5 : (0 <= mask_pre)) (PreH6 : (mask_pre < 1073741824)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i left 0)) /\ ((Znth i left 0) < 1073741824)))) (PreH8 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) < 1073741824)))) ,
  forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))
.

Definition feasible_entail_wit_1_split_goal_3 := 
forall (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (left)))) (PreH4 : ((Zlength (right)) = n_pre)) (PreH5 : (0 <= mask_pre)) (PreH6 : (mask_pre < 1073741824)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i left 0)) /\ ((Znth i left 0) < 1073741824)))) (PreH8 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) < 1073741824)))) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))
.

Definition feasible_entail_wit_2 := 
(
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : (0 <= mask_pre)) (PreH7 : (mask_pre < 1073741824)) (PreH8 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> ((0 <= (Znth j_3 left 0)) /\ ((Znth j_3 left 0) < 1073741824)))) (PreH9 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((0 <= (Znth j_4 right 0)) /\ ((Znth j_4 right 0) < 1073741824)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values i )) ,
  (UIntArray.seg kb_pre 0 (i + 1 ) (app (kb_values) ((cons ((Z.land (Z.lnot (Znth i right 0)) mask_pre)) ((@nil Z))))) )
  **  (UIntArray.undef_seg kb_pre (i + 1 ) n_pre )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.seg ka_pre 0 (i + 1 ) (app (ka_values) ((cons ((Z.land (Znth i left 0) mask_pre)) ((@nil Z))))) )
  **  (UIntArray.undef_seg ka_pre (i + 1 ) n_pre )
  **  (UIntArray.full a_pre n_pre left )
|--
  EX (ka_next: (@list Z))  (kb_next: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ (0 <= mask_pre) ” 
  &&  “ (mask_pre < 1073741824) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (MaskedBuffersPrefix left right mask_pre ka_next kb_next (i + 1 ) ) ”
  &&  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.seg ka_pre 0 (i + 1 ) ka_next )
  **  (UIntArray.undef_seg ka_pre (i + 1 ) n_pre )
  **  (UIntArray.seg kb_pre 0 (i + 1 ) kb_next )
  **  (UIntArray.undef_seg kb_pre (i + 1 ) n_pre )
) \/
(
forall (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : (0 <= mask_pre)) (PreH7 : (mask_pre < 1073741824)) (PreH8 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> ((0 <= (Znth j_3 left 0)) /\ ((Znth j_3 left 0) < 1073741824)))) (PreH9 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((0 <= (Znth j_4 right 0)) /\ ((Znth j_4 right 0) < 1073741824)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values i )) ,
  TT && emp 
|--
  “ (MaskedBuffersPrefix left right mask_pre (app (ka_values) ((cons ((Z.land (Znth i left 0) mask_pre)) ((@nil Z))))) (app (kb_values) ((cons ((Z.land (Z.lnot (Znth i right 0)) mask_pre)) ((@nil Z))))) (i + 1 ) ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ”
  &&  emp
).

Definition feasible_entail_wit_2_split_goal_1 := 
forall (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : (0 <= mask_pre)) (PreH7 : (mask_pre < 1073741824)) (PreH8 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> ((0 <= (Znth j_3 left 0)) /\ ((Znth j_3 left 0) < 1073741824)))) (PreH9 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((0 <= (Znth j_4 right 0)) /\ ((Znth j_4 right 0) < 1073741824)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values i )) ,
  (MaskedBuffersPrefix left right mask_pre (app (ka_values) ((cons ((Z.land (Znth i left 0) mask_pre)) ((@nil Z))))) (app (kb_values) ((cons ((Z.land (Z.lnot (Znth i right 0)) mask_pre)) ((@nil Z))))) (i + 1 ) )
.

Definition feasible_entail_wit_2_split_goal_2 := 
forall (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : (0 <= mask_pre)) (PreH7 : (mask_pre < 1073741824)) (PreH8 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> ((0 <= (Znth j_3 left 0)) /\ ((Znth j_3 left 0) < 1073741824)))) (PreH9 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((0 <= (Znth j_4 right 0)) /\ ((Znth j_4 right 0) < 1073741824)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values i )) ,
  forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))
.

Definition feasible_entail_wit_2_split_goal_3 := 
forall (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : (0 <= mask_pre)) (PreH7 : (mask_pre < 1073741824)) (PreH8 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> ((0 <= (Znth j_3 left 0)) /\ ((Znth j_3 left 0) < 1073741824)))) (PreH9 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((0 <= (Znth j_4 right 0)) /\ ((Znth j_4 right 0) < 1073741824)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values i )) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))
.

Definition feasible_entail_wit_3 := 
(
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_next: (@list Z)) (kb_next: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (left)))) (PreH4 : ((Zlength (right)) = n_pre)) (PreH5 : (0 <= mask_pre)) (PreH6 : (mask_pre < 1073741824)) (PreH7 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> ((0 <= (Znth j_3 left 0)) /\ ((Znth j_3 left 0) < 1073741824)))) (PreH8 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((0 <= (Znth j_4 right 0)) /\ ((Znth j_4 right 0) < 1073741824)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (MaskedBuffersPrefix left right mask_pre ka_next kb_next (i + 1 ) )) ,
  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.seg ka_pre 0 (i + 1 ) ka_next )
  **  (UIntArray.undef_seg ka_pre (i + 1 ) n_pre )
  **  (UIntArray.seg kb_pre 0 (i + 1 ) kb_next )
  **  (UIntArray.undef_seg kb_pre (i + 1 ) n_pre )
|--
  EX (ka_values: (@list Z))  (kb_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ (0 <= mask_pre) ” 
  &&  “ (mask_pre < 1073741824) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (MaskedBuffersPrefix left right mask_pre ka_values kb_values (i + 1 ) ) ”
  &&  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.seg ka_pre 0 (i + 1 ) ka_values )
  **  (UIntArray.undef_seg ka_pre (i + 1 ) n_pre )
  **  (UIntArray.seg kb_pre 0 (i + 1 ) kb_values )
  **  (UIntArray.undef_seg kb_pre (i + 1 ) n_pre )
) \/
(
forall (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_next: (@list Z)) (kb_next: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (left)))) (PreH4 : ((Zlength (right)) = n_pre)) (PreH5 : (0 <= mask_pre)) (PreH6 : (mask_pre < 1073741824)) (PreH7 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> ((0 <= (Znth j_3 left 0)) /\ ((Znth j_3 left 0) < 1073741824)))) (PreH8 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((0 <= (Znth j_4 right 0)) /\ ((Znth j_4 right 0) < 1073741824)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (MaskedBuffersPrefix left right mask_pre ka_next kb_next (i + 1 ) )) ,
  TT && emp 
|--
  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ”
  &&  emp
).

Definition feasible_entail_wit_3_split_goal_1 := 
forall (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_next: (@list Z)) (kb_next: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (left)))) (PreH4 : ((Zlength (right)) = n_pre)) (PreH5 : (0 <= mask_pre)) (PreH6 : (mask_pre < 1073741824)) (PreH7 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> ((0 <= (Znth j_3 left 0)) /\ ((Znth j_3 left 0) < 1073741824)))) (PreH8 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((0 <= (Znth j_4 right 0)) /\ ((Znth j_4 right 0) < 1073741824)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (MaskedBuffersPrefix left right mask_pre ka_next kb_next (i + 1 ) )) ,
  forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))
.

Definition feasible_entail_wit_3_split_goal_2 := 
forall (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_next: (@list Z)) (kb_next: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (left)))) (PreH4 : ((Zlength (right)) = n_pre)) (PreH5 : (0 <= mask_pre)) (PreH6 : (mask_pre < 1073741824)) (PreH7 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> ((0 <= (Znth j_3 left 0)) /\ ((Znth j_3 left 0) < 1073741824)))) (PreH8 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((0 <= (Znth j_4 right 0)) /\ ((Znth j_4 right 0) < 1073741824)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (MaskedBuffersPrefix left right mask_pre ka_next kb_next (i + 1 ) )) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))
.

Definition feasible_entail_wit_4 := 
(
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values_2: (@list Z)) (kb_values_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : (0 <= mask_pre)) (PreH7 : (mask_pre < 1073741824)) (PreH8 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> ((0 <= (Znth j_3 left 0)) /\ ((Znth j_3 left 0) < 1073741824)))) (PreH9 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((0 <= (Znth j_4 right 0)) /\ ((Znth j_4 right 0) < 1073741824)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (MaskedBuffersPrefix left right mask_pre ka_values_2 kb_values_2 i )) ,
  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.seg ka_pre 0 i ka_values_2 )
  **  (UIntArray.undef_seg ka_pre i n_pre )
  **  (UIntArray.seg kb_pre 0 i kb_values_2 )
  **  (UIntArray.undef_seg kb_pre i n_pre )
|--
  EX (ka_values: (@list Z))  (kb_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ (0 <= mask_pre) ” 
  &&  “ (mask_pre < 1073741824) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre ) ”
  &&  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full ka_pre n_pre ka_values )
  **  (UIntArray.full kb_pre n_pre kb_values )
) \/
(
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values_2: (@list Z)) (kb_values_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : (0 <= mask_pre)) (PreH7 : (mask_pre < 1073741824)) (PreH8 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> ((0 <= (Znth j_3 left 0)) /\ ((Znth j_3 left 0) < 1073741824)))) (PreH9 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((0 <= (Znth j_4 right 0)) /\ ((Znth j_4 right 0) < 1073741824)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (MaskedBuffersPrefix left right mask_pre ka_values_2 kb_values_2 i )) ,
  (UIntArray.seg ka_pre 0 i ka_values_2 )
  **  (UIntArray.seg kb_pre 0 i kb_values_2 )
|--
  EX (ka_values: (@list Z))  (kb_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ (0 <= mask_pre) ” 
  &&  “ (mask_pre < 1073741824) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre ) ”
  &&  (UIntArray.full ka_pre n_pre ka_values )
  **  (UIntArray.full kb_pre n_pre kb_values )
).

Definition feasible_entail_wit_5 := 
(
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values_2: (@list Z)) (kb_values_2: (@list Z)) (l1: (@list Z)) (l1_2: (@list Z)) (PreH1 : (Permutation kb_values_2 l1_2 )) (PreH2 : (mono_nondec l1_2 )) (PreH3 : (Permutation ka_values_2 l1 )) (PreH4 : (mono_nondec l1 )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (left)))) (PreH8 : ((Zlength (right)) = n_pre)) (PreH9 : (0 <= mask_pre)) (PreH10 : (mask_pre < 1073741824)) (PreH11 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> ((0 <= (Znth j_3 left 0)) /\ ((Znth j_3 left 0) < 1073741824)))) (PreH12 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((0 <= (Znth j_4 right 0)) /\ ((Znth j_4 right 0) < 1073741824)))) (PreH13 : (MaskedBuffersPrefix left right mask_pre ka_values_2 kb_values_2 n_pre )) ,
  (UIntArray.full kb_pre n_pre l1_2 )
  **  (UIntArray.full ka_pre n_pre l1 )
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
|--
  EX (sorted_kb: (@list Z))  (sorted_ka: (@list Z))  (ka_values: (@list Z))  (kb_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ (0 <= mask_pre) ” 
  &&  “ (mask_pre < 1073741824) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre ) ” 
  &&  “ (Permutation ka_values sorted_ka ) ” 
  &&  “ (Permutation kb_values sorted_kb ) ” 
  &&  “ (mono_nondec sorted_ka ) ” 
  &&  “ (mono_nondec sorted_kb ) ”
  &&  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full ka_pre n_pre sorted_ka )
  **  (UIntArray.full kb_pre n_pre sorted_kb )
) \/
(
forall (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values_2: (@list Z)) (kb_values_2: (@list Z)) (l1: (@list Z)) (l1_2: (@list Z)) (PreH1 : (Permutation kb_values_2 l1_2 )) (PreH2 : (mono_nondec l1_2 )) (PreH3 : (Permutation ka_values_2 l1 )) (PreH4 : (mono_nondec l1 )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (left)))) (PreH8 : ((Zlength (right)) = n_pre)) (PreH9 : (0 <= mask_pre)) (PreH10 : (mask_pre < 1073741824)) (PreH11 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> ((0 <= (Znth j_3 left 0)) /\ ((Znth j_3 left 0) < 1073741824)))) (PreH12 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((0 <= (Znth j_4 right 0)) /\ ((Znth j_4 right 0) < 1073741824)))) (PreH13 : (MaskedBuffersPrefix left right mask_pre ka_values_2 kb_values_2 n_pre )) ,
  TT && emp 
|--
  EX (ka_values: (@list Z))  (kb_values: (@list Z)) ,
  “ (MaskedBuffersPrefix left right mask_pre ka_values kb_values (Zlength (left)) ) ” 
  &&  “ (Permutation ka_values l1 ) ” 
  &&  “ (Permutation kb_values l1_2 ) ”
  &&  emp
).

Definition feasible_entail_wit_6 := 
(
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values_2: (@list Z)) (kb_values_2: (@list Z)) (sorted_ka_2: (@list Z)) (sorted_kb_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (left)))) (PreH4 : ((Zlength (right)) = n_pre)) (PreH5 : (0 <= mask_pre)) (PreH6 : (mask_pre < 1073741824)) (PreH7 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> ((0 <= (Znth j_3 left 0)) /\ ((Znth j_3 left 0) < 1073741824)))) (PreH8 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((0 <= (Znth j_4 right 0)) /\ ((Znth j_4 right 0) < 1073741824)))) (PreH9 : (MaskedBuffersPrefix left right mask_pre ka_values_2 kb_values_2 n_pre )) (PreH10 : (Permutation ka_values_2 sorted_ka_2 )) (PreH11 : (Permutation kb_values_2 sorted_kb_2 )) (PreH12 : (mono_nondec sorted_ka_2 )) (PreH13 : (mono_nondec sorted_kb_2 )) ,
  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full ka_pre n_pre sorted_ka_2 )
  **  (UIntArray.full kb_pre n_pre sorted_kb_2 )
|--
  EX (sorted_kb: (@list Z))  (sorted_ka: (@list Z))  (ka_values: (@list Z))  (kb_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ (0 <= mask_pre) ” 
  &&  “ (mask_pre < 1073741824) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre ) ” 
  &&  “ (Permutation ka_values sorted_ka ) ” 
  &&  “ (Permutation kb_values sorted_kb ) ” 
  &&  “ (mono_nondec sorted_ka ) ” 
  &&  “ (mono_nondec sorted_kb ) ” 
  &&  “ ((sublist (0) (0) (sorted_ka)) = (sublist (0) (0) (sorted_kb))) ”
  &&  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full ka_pre n_pre sorted_ka )
  **  (UIntArray.full kb_pre n_pre sorted_kb )
) \/
(
forall (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values_2: (@list Z)) (kb_values_2: (@list Z)) (sorted_ka_2: (@list Z)) (sorted_kb_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (left)))) (PreH4 : ((Zlength (right)) = n_pre)) (PreH5 : (0 <= mask_pre)) (PreH6 : (mask_pre < 1073741824)) (PreH7 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> ((0 <= (Znth j_3 left 0)) /\ ((Znth j_3 left 0) < 1073741824)))) (PreH8 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((0 <= (Znth j_4 right 0)) /\ ((Znth j_4 right 0) < 1073741824)))) (PreH9 : (MaskedBuffersPrefix left right mask_pre ka_values_2 kb_values_2 n_pre )) (PreH10 : (Permutation ka_values_2 sorted_ka_2 )) (PreH11 : (Permutation kb_values_2 sorted_kb_2 )) (PreH12 : (mono_nondec sorted_ka_2 )) (PreH13 : (mono_nondec sorted_kb_2 )) ,
  TT && emp 
|--
  EX (ka_values: (@list Z))  (kb_values: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength (left))) ” 
  &&  “ (MaskedBuffersPrefix left right mask_pre ka_values kb_values (Zlength (left)) ) ” 
  &&  “ (Permutation ka_values sorted_ka_2 ) ” 
  &&  “ (Permutation kb_values sorted_kb_2 ) ” 
  &&  “ ((sublist (0) (0) (sorted_ka_2)) = (sublist (0) (0) (sorted_kb_2))) ”
  &&  emp
).

Definition feasible_entail_wit_7 := 
(
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (sorted_kb_2: (@list Z)) (sorted_ka_2: (@list Z)) (ka_values_2: (@list Z)) (kb_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth i sorted_ka_2 0) = (Znth i sorted_kb_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : ((Zlength (right)) = n_pre)) (PreH7 : (0 <= mask_pre)) (PreH8 : (mask_pre < 1073741824)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH10 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (MaskedBuffersPrefix left right mask_pre ka_values_2 kb_values_2 n_pre )) (PreH14 : (Permutation ka_values_2 sorted_ka_2 )) (PreH15 : (Permutation kb_values_2 sorted_kb_2 )) (PreH16 : (mono_nondec sorted_ka_2 )) (PreH17 : (mono_nondec sorted_kb_2 )) (PreH18 : ((sublist (0) (i) (sorted_ka_2)) = (sublist (0) (i) (sorted_kb_2)))) ,
  (UIntArray.full kb_pre n_pre sorted_kb_2 )
  **  (UIntArray.full ka_pre n_pre sorted_ka_2 )
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
|--
  EX (sorted_kb: (@list Z))  (sorted_ka: (@list Z))  (ka_values: (@list Z))  (kb_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ (0 <= mask_pre) ” 
  &&  “ (mask_pre < 1073741824) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre ) ” 
  &&  “ (Permutation ka_values sorted_ka ) ” 
  &&  “ (Permutation kb_values sorted_kb ) ” 
  &&  “ (mono_nondec sorted_ka ) ” 
  &&  “ (mono_nondec sorted_kb ) ” 
  &&  “ ((sublist (0) ((i + 1 )) (sorted_ka)) = (sublist (0) ((i + 1 )) (sorted_kb))) ”
  &&  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full ka_pre n_pre sorted_ka )
  **  (UIntArray.full kb_pre n_pre sorted_kb )
) \/
(
forall (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (sorted_kb_2: (@list Z)) (sorted_ka_2: (@list Z)) (ka_values_2: (@list Z)) (kb_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth i sorted_ka_2 0) = (Znth i sorted_kb_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : ((Zlength (right)) = n_pre)) (PreH7 : (0 <= mask_pre)) (PreH8 : (mask_pre < 1073741824)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH10 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (MaskedBuffersPrefix left right mask_pre ka_values_2 kb_values_2 n_pre )) (PreH14 : (Permutation ka_values_2 sorted_ka_2 )) (PreH15 : (Permutation kb_values_2 sorted_kb_2 )) (PreH16 : (mono_nondec sorted_ka_2 )) (PreH17 : (mono_nondec sorted_kb_2 )) (PreH18 : ((sublist (0) (i) (sorted_ka_2)) = (sublist (0) (i) (sorted_kb_2)))) ,
  TT && emp 
|--
  EX (ka_values: (@list Z))  (kb_values: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (left))) ” 
  &&  “ (MaskedBuffersPrefix left right mask_pre ka_values kb_values (Zlength (left)) ) ” 
  &&  “ (Permutation ka_values sorted_ka_2 ) ” 
  &&  “ (Permutation kb_values sorted_kb_2 ) ” 
  &&  “ ((sublist (0) ((i + 1 )) (sorted_ka_2)) = (sublist (0) ((i + 1 )) (sorted_kb_2))) ”
  &&  emp
).

Definition feasible_return_wit_1 := 
(
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (sorted_kb: (@list Z)) (sorted_ka: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : (0 <= mask_pre)) (PreH7 : (mask_pre < 1073741824)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre )) (PreH13 : (Permutation ka_values sorted_ka )) (PreH14 : (Permutation kb_values sorted_kb )) (PreH15 : (mono_nondec sorted_ka )) (PreH16 : (mono_nondec sorted_kb )) (PreH17 : ((sublist (0) (i) (sorted_ka)) = (sublist (0) (i) (sorted_kb)))) ,
  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full ka_pre n_pre sorted_ka )
  **  (UIntArray.full kb_pre n_pre sorted_kb )
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ ((1 = 1) -> (MaskFeasible left right mask_pre )) ” 
  &&  “ ((1 = 0) -> ~((MaskFeasible left right mask_pre ))) ”
  &&  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full_shape ka_pre n_pre )
  **  (UIntArray.full_shape kb_pre n_pre )
) \/
(
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (sorted_kb: (@list Z)) (sorted_ka: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : (0 <= mask_pre)) (PreH7 : (mask_pre < 1073741824)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre )) (PreH13 : (Permutation ka_values sorted_ka )) (PreH14 : (Permutation kb_values sorted_kb )) (PreH15 : (mono_nondec sorted_ka )) (PreH16 : (mono_nondec sorted_kb )) (PreH17 : ((sublist (0) (i) (sorted_ka)) = (sublist (0) (i) (sorted_kb)))) ,
  (UIntArray.full ka_pre n_pre sorted_ka )
  **  (UIntArray.full kb_pre n_pre sorted_kb )
|--
  “ ((1 = 1) -> (MaskFeasible left right mask_pre )) ”
  &&  (UIntArray.full_shape ka_pre n_pre )
  **  (UIntArray.full_shape kb_pre n_pre )
).

Definition feasible_return_wit_1_split_goal_1 := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (sorted_kb: (@list Z)) (sorted_ka: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : (0 <= mask_pre)) (PreH7 : (mask_pre < 1073741824)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre )) (PreH13 : (Permutation ka_values sorted_ka )) (PreH14 : (Permutation kb_values sorted_kb )) (PreH15 : (mono_nondec sorted_ka )) (PreH16 : (mono_nondec sorted_kb )) (PreH17 : ((sublist (0) (i) (sorted_ka)) = (sublist (0) (i) (sorted_kb)))) ,
  (UIntArray.full ka_pre n_pre sorted_ka )
  **  (UIntArray.full kb_pre n_pre sorted_kb )
|--
  “ ((1 = 1) -> (MaskFeasible left right mask_pre )) ”
.

Definition feasible_return_wit_1_split_goal_spatial := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (sorted_kb: (@list Z)) (sorted_ka: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : (0 <= mask_pre)) (PreH7 : (mask_pre < 1073741824)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre )) (PreH13 : (Permutation ka_values sorted_ka )) (PreH14 : (Permutation kb_values sorted_kb )) (PreH15 : (mono_nondec sorted_ka )) (PreH16 : (mono_nondec sorted_kb )) (PreH17 : ((sublist (0) (i) (sorted_ka)) = (sublist (0) (i) (sorted_kb)))) ,
  (UIntArray.full ka_pre n_pre sorted_ka )
  **  (UIntArray.full kb_pre n_pre sorted_kb )
|--
  (UIntArray.full_shape ka_pre n_pre )
  **  (UIntArray.full_shape kb_pre n_pre )
.

Definition feasible_return_wit_2 := 
(
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (sorted_kb: (@list Z)) (sorted_ka: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : ((Znth i sorted_ka 0) <> (Znth i sorted_kb 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : ((Zlength (right)) = n_pre)) (PreH7 : (0 <= mask_pre)) (PreH8 : (mask_pre < 1073741824)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH10 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre )) (PreH14 : (Permutation ka_values sorted_ka )) (PreH15 : (Permutation kb_values sorted_kb )) (PreH16 : (mono_nondec sorted_ka )) (PreH17 : (mono_nondec sorted_kb )) (PreH18 : ((sublist (0) (i) (sorted_ka)) = (sublist (0) (i) (sorted_kb)))) ,
  (UIntArray.full kb_pre n_pre sorted_kb )
  **  (UIntArray.full ka_pre n_pre sorted_ka )
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((0 = 1) -> (MaskFeasible left right mask_pre )) ” 
  &&  “ ((0 = 0) -> ~((MaskFeasible left right mask_pre ))) ”
  &&  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full_shape ka_pre n_pre )
  **  (UIntArray.full_shape kb_pre n_pre )
) \/
(
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (sorted_kb: (@list Z)) (sorted_ka: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : ((Znth i sorted_ka 0) <> (Znth i sorted_kb 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : ((Zlength (right)) = n_pre)) (PreH7 : (0 <= mask_pre)) (PreH8 : (mask_pre < 1073741824)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH10 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre )) (PreH14 : (Permutation ka_values sorted_ka )) (PreH15 : (Permutation kb_values sorted_kb )) (PreH16 : (mono_nondec sorted_ka )) (PreH17 : (mono_nondec sorted_kb )) (PreH18 : ((sublist (0) (i) (sorted_ka)) = (sublist (0) (i) (sorted_kb)))) ,
  (UIntArray.full kb_pre n_pre sorted_kb )
  **  (UIntArray.full ka_pre n_pre sorted_ka )
|--
  “ ((0 = 0) -> ~((MaskFeasible left right mask_pre ))) ”
  &&  (UIntArray.full_shape ka_pre n_pre )
  **  (UIntArray.full_shape kb_pre n_pre )
).

Definition feasible_return_wit_2_split_goal_1 := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (sorted_kb: (@list Z)) (sorted_ka: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : ((Znth i sorted_ka 0) <> (Znth i sorted_kb 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : ((Zlength (right)) = n_pre)) (PreH7 : (0 <= mask_pre)) (PreH8 : (mask_pre < 1073741824)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH10 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre )) (PreH14 : (Permutation ka_values sorted_ka )) (PreH15 : (Permutation kb_values sorted_kb )) (PreH16 : (mono_nondec sorted_ka )) (PreH17 : (mono_nondec sorted_kb )) (PreH18 : ((sublist (0) (i) (sorted_ka)) = (sublist (0) (i) (sorted_kb)))) ,
  (UIntArray.full kb_pre n_pre sorted_kb )
  **  (UIntArray.full ka_pre n_pre sorted_ka )
|--
  “ ((0 = 0) -> ~((MaskFeasible left right mask_pre ))) ”
.

Definition feasible_return_wit_2_split_goal_spatial := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (sorted_kb: (@list Z)) (sorted_ka: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : ((Znth i sorted_ka 0) <> (Znth i sorted_kb 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : ((Zlength (right)) = n_pre)) (PreH7 : (0 <= mask_pre)) (PreH8 : (mask_pre < 1073741824)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH10 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre )) (PreH14 : (Permutation ka_values sorted_ka )) (PreH15 : (Permutation kb_values sorted_kb )) (PreH16 : (mono_nondec sorted_ka )) (PreH17 : (mono_nondec sorted_kb )) (PreH18 : ((sublist (0) (i) (sorted_ka)) = (sublist (0) (i) (sorted_kb)))) ,
  (UIntArray.full kb_pre n_pre sorted_kb )
  **  (UIntArray.full ka_pre n_pre sorted_ka )
|--
  (UIntArray.full_shape ka_pre n_pre )
  **  (UIntArray.full_shape kb_pre n_pre )
.

Definition feasible_partial_solve_wit_1 := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : (0 <= mask_pre)) (PreH7 : (mask_pre < 1073741824)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values i )) ,
  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.seg ka_pre 0 i ka_values )
  **  (UIntArray.undef_seg ka_pre i n_pre )
  **  (UIntArray.seg kb_pre 0 i kb_values )
  **  (UIntArray.undef_seg kb_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ (0 <= mask_pre) ” 
  &&  “ (mask_pre < 1073741824) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (MaskedBuffersPrefix left right mask_pre ka_values kb_values i ) ”
  &&  (((a_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i left 0))
  **  (UIntArray.missing_i a_pre i 0 n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.seg ka_pre 0 i ka_values )
  **  (UIntArray.undef_seg ka_pre i n_pre )
  **  (UIntArray.seg kb_pre 0 i kb_values )
  **  (UIntArray.undef_seg kb_pre i n_pre )
.

Definition feasible_partial_solve_wit_2 := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : (0 <= mask_pre)) (PreH7 : (mask_pre < 1073741824)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values i )) ,
  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.seg ka_pre 0 i ka_values )
  **  (UIntArray.undef_seg ka_pre i n_pre )
  **  (UIntArray.seg kb_pre 0 i kb_values )
  **  (UIntArray.undef_seg kb_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ (0 <= mask_pre) ” 
  &&  “ (mask_pre < 1073741824) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (MaskedBuffersPrefix left right mask_pre ka_values kb_values i ) ”
  &&  (((ka_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg ka_pre (i + 1 ) n_pre )
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.seg ka_pre 0 i ka_values )
  **  (UIntArray.seg kb_pre 0 i kb_values )
  **  (UIntArray.undef_seg kb_pre i n_pre )
.

Definition feasible_partial_solve_wit_3 := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : (0 <= mask_pre)) (PreH7 : (mask_pre < 1073741824)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values i )) ,
  (UIntArray.seg ka_pre 0 (i + 1 ) (app (ka_values) ((cons ((Z.land (Znth i left 0) mask_pre)) ((@nil Z))))) )
  **  (UIntArray.undef_seg ka_pre (i + 1 ) n_pre )
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.seg kb_pre 0 i kb_values )
  **  (UIntArray.undef_seg kb_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ (0 <= mask_pre) ” 
  &&  “ (mask_pre < 1073741824) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (MaskedBuffersPrefix left right mask_pre ka_values kb_values i ) ”
  &&  (((b_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i right 0))
  **  (UIntArray.missing_i b_pre i 0 n_pre right )
  **  (UIntArray.seg ka_pre 0 (i + 1 ) (app (ka_values) ((cons ((Z.land (Znth i left 0) mask_pre)) ((@nil Z))))) )
  **  (UIntArray.undef_seg ka_pre (i + 1 ) n_pre )
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.seg kb_pre 0 i kb_values )
  **  (UIntArray.undef_seg kb_pre i n_pre )
.

Definition feasible_partial_solve_wit_4 := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : (0 <= mask_pre)) (PreH7 : (mask_pre < 1073741824)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values i )) ,
  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.seg ka_pre 0 (i + 1 ) (app (ka_values) ((cons ((Z.land (Znth i left 0) mask_pre)) ((@nil Z))))) )
  **  (UIntArray.undef_seg ka_pre (i + 1 ) n_pre )
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.seg kb_pre 0 i kb_values )
  **  (UIntArray.undef_seg kb_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ (0 <= mask_pre) ” 
  &&  “ (mask_pre < 1073741824) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (MaskedBuffersPrefix left right mask_pre ka_values kb_values i ) ”
  &&  (((kb_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg kb_pre (i + 1 ) n_pre )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.seg ka_pre 0 (i + 1 ) (app (ka_values) ((cons ((Z.land (Znth i left 0) mask_pre)) ((@nil Z))))) )
  **  (UIntArray.undef_seg ka_pre (i + 1 ) n_pre )
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.seg kb_pre 0 i kb_values )
.

Definition feasible_partial_solve_wit_5_pure := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (left)))) (PreH4 : ((Zlength (right)) = n_pre)) (PreH5 : (0 <= mask_pre)) (PreH6 : (mask_pre < 1073741824)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH9 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mask" ) )) # UInt  |-> mask_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full ka_pre n_pre ka_values )
  **  (UIntArray.full kb_pre n_pre kb_values )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ”
.

Definition feasible_partial_solve_wit_5_aux := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (left)))) (PreH4 : ((Zlength (right)) = n_pre)) (PreH5 : (0 <= mask_pre)) (PreH6 : (mask_pre < 1073741824)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH9 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre )) ,
  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full ka_pre n_pre ka_values )
  **  (UIntArray.full kb_pre n_pre kb_values )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ (0 <= mask_pre) ” 
  &&  “ (mask_pre < 1073741824) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre ) ”
  &&  (UIntArray.full ka_pre n_pre ka_values )
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full kb_pre n_pre kb_values )
.

Definition feasible_partial_solve_wit_5 := feasible_partial_solve_wit_5_pure -> feasible_partial_solve_wit_5_aux.

Definition feasible_partial_solve_wit_6_pure := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (l1: (@list Z)) (PreH1 : (Permutation ka_values l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : ((Zlength (right)) = n_pre)) (PreH7 : (0 <= mask_pre)) (PreH8 : (mask_pre < 1073741824)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH10 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH11 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre )) ,
  (UIntArray.full ka_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "mask" ) )) # UInt  |-> mask_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full kb_pre n_pre kb_values )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ”
.

Definition feasible_partial_solve_wit_6_aux := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (l1: (@list Z)) (PreH1 : (Permutation ka_values l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : ((Zlength (right)) = n_pre)) (PreH7 : (0 <= mask_pre)) (PreH8 : (mask_pre < 1073741824)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH10 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH11 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre )) ,
  (UIntArray.full ka_pre n_pre l1 )
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full kb_pre n_pre kb_values )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (Permutation ka_values l1 ) ” 
  &&  “ (mono_nondec l1 ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ (0 <= mask_pre) ” 
  &&  “ (mask_pre < 1073741824) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre ) ”
  &&  (UIntArray.full kb_pre n_pre kb_values )
  **  (UIntArray.full ka_pre n_pre l1 )
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
.

Definition feasible_partial_solve_wit_6 := feasible_partial_solve_wit_6_pure -> feasible_partial_solve_wit_6_aux.

Definition feasible_partial_solve_wit_7 := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (sorted_kb: (@list Z)) (sorted_ka: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : (0 <= mask_pre)) (PreH7 : (mask_pre < 1073741824)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre )) (PreH13 : (Permutation ka_values sorted_ka )) (PreH14 : (Permutation kb_values sorted_kb )) (PreH15 : (mono_nondec sorted_ka )) (PreH16 : (mono_nondec sorted_kb )) (PreH17 : ((sublist (0) (i) (sorted_ka)) = (sublist (0) (i) (sorted_kb)))) ,
  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full ka_pre n_pre sorted_ka )
  **  (UIntArray.full kb_pre n_pre sorted_kb )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ (0 <= mask_pre) ” 
  &&  “ (mask_pre < 1073741824) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre ) ” 
  &&  “ (Permutation ka_values sorted_ka ) ” 
  &&  “ (Permutation kb_values sorted_kb ) ” 
  &&  “ (mono_nondec sorted_ka ) ” 
  &&  “ (mono_nondec sorted_kb ) ” 
  &&  “ ((sublist (0) (i) (sorted_ka)) = (sublist (0) (i) (sorted_kb))) ”
  &&  (((ka_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i sorted_ka 0))
  **  (UIntArray.missing_i ka_pre i 0 n_pre sorted_ka )
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full kb_pre n_pre sorted_kb )
.

Definition feasible_partial_solve_wit_8 := 
forall (kb_pre: Z) (ka_pre: Z) (mask_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (sorted_kb: (@list Z)) (sorted_ka: (@list Z)) (ka_values: (@list Z)) (kb_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : (0 <= mask_pre)) (PreH7 : (mask_pre < 1073741824)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre )) (PreH13 : (Permutation ka_values sorted_ka )) (PreH14 : (Permutation kb_values sorted_kb )) (PreH15 : (mono_nondec sorted_ka )) (PreH16 : (mono_nondec sorted_kb )) (PreH17 : ((sublist (0) (i) (sorted_ka)) = (sublist (0) (i) (sorted_kb)))) ,
  (UIntArray.full ka_pre n_pre sorted_ka )
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full kb_pre n_pre sorted_kb )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ (0 <= mask_pre) ” 
  &&  “ (mask_pre < 1073741824) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (MaskedBuffersPrefix left right mask_pre ka_values kb_values n_pre ) ” 
  &&  “ (Permutation ka_values sorted_ka ) ” 
  &&  “ (Permutation kb_values sorted_kb ) ” 
  &&  “ (mono_nondec sorted_ka ) ” 
  &&  “ (mono_nondec sorted_kb ) ” 
  &&  “ ((sublist (0) (i) (sorted_ka)) = (sublist (0) (i) (sorted_kb))) ”
  &&  (((kb_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i sorted_kb 0))
  **  (UIntArray.missing_i kb_pre i 0 n_pre sorted_kb )
  **  (UIntArray.full ka_pre n_pre sorted_ka )
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i left 0)) /\ ((Znth i left 0) < 1073741824)))) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) < 1073741824)))) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : ((Zlength (right)) = n_pre)) ,
  ((( &( "ans" ) )) # UInt  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i left 0)) /\ ((Znth i left 0) < 1073741824)))) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) < 1073741824)))) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : ((Zlength (right)) = n_pre)) ,
  ((( &( "bit" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # UInt  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre )
|--
  “ (29 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 29) ”
.

Definition solver_safety_wit_3 := 
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (left)))) (PreH4 : ((Zlength (right)) = n_pre)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH7 : ((-1) <= bit)) (PreH8 : (bit <= 29)) (PreH9 : (0 <= ans)) (PreH10 : (ans < 1073741824)) (PreH11 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH12 : (0 <= bit)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "ans" ) )) # UInt  |-> ans)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (left)))) (PreH4 : ((Zlength (right)) = n_pre)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH7 : ((-1) <= bit)) (PreH8 : (bit <= 29)) (PreH9 : (0 <= ans)) (PreH10 : (ans < 1073741824)) (PreH11 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH12 : (bit = (-1))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "ans" ) )) # UInt  |-> ans)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full_shape ka_pre n_pre )
  **  (UIntArray.full_shape kb_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 := 
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (PreH1 : (bit < 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH7 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH8 : ((-1) <= bit)) (PreH9 : (bit <= 29)) (PreH10 : (0 <= ans)) (PreH11 : (ans < 1073741824)) (PreH12 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH13 : (0 <= bit)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "ans" ) )) # UInt  |-> ans)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre )
|--
  “ False ”
.

Definition solver_safety_wit_6 := 
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (PreH1 : (bit >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH7 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH8 : ((-1) <= bit)) (PreH9 : (bit <= 29)) (PreH10 : (0 <= ans)) (PreH11 : (ans < 1073741824)) (PreH12 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH13 : (bit = (-1))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "ans" ) )) # UInt  |-> ans)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full_shape ka_pre n_pre )
  **  (UIntArray.full_shape kb_pre n_pre )
|--
  “ False ”
.

Definition solver_safety_wit_7 := 
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (PreH1 : (bit >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH7 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH8 : ((-1) <= bit)) (PreH9 : (bit <= 29)) (PreH10 : (0 <= ans)) (PreH11 : (ans < 1073741824)) (PreH12 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH13 : (0 <= bit)) ,
  ((( &( "cand" ) )) # UInt  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "ans" ) )) # UInt  |-> ans)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre )
|--
  “ (bit <= 31) ” 
  &&  “ (0 <= bit) ”
.

Definition solver_safety_wit_8 := 
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (MaskFeasible left right (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) ))) (PreH4 : ((retval = 0) -> ~((MaskFeasible left right (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) )))) (PreH5 : (0 <= (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))))) (PreH6 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) < 1073741824)) (PreH7 : (ans <= UINT_MAX)) (PreH8 : (ans >= 0)) (PreH9 : (bit <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (bit >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (bit >= 0)) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : (n_pre = (Zlength (left)))) (PreH17 : ((Zlength (right)) = n_pre)) (PreH18 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH20 : ((-1) <= bit)) (PreH21 : (bit <= 29)) (PreH22 : (0 <= ans)) (PreH23 : (ans < 1073741824)) (PreH24 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH25 : (0 <= bit)) (PreH26 : (retval <> 0)) ,
  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full_shape ka_pre n_pre )
  **  (UIntArray.full_shape kb_pre n_pre )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "ans" ) )) # UInt  |-> (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))))
|--
  “ ((bit - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bit - 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (MaskFeasible left right (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) ))) (PreH4 : ((retval = 0) -> ~((MaskFeasible left right (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) )))) (PreH5 : (0 <= (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))))) (PreH6 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) < 1073741824)) (PreH7 : (ans <= UINT_MAX)) (PreH8 : (ans >= 0)) (PreH9 : (bit <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (bit >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (bit >= 0)) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : (n_pre = (Zlength (left)))) (PreH17 : ((Zlength (right)) = n_pre)) (PreH18 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH20 : ((-1) <= bit)) (PreH21 : (bit <= 29)) (PreH22 : (0 <= ans)) (PreH23 : (ans < 1073741824)) (PreH24 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH25 : (0 <= bit)) (PreH26 : (retval = 0)) ,
  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full_shape ka_pre n_pre )
  **  (UIntArray.full_shape kb_pre n_pre )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "ans" ) )) # UInt  |-> ans)
|--
  “ ((bit - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bit - 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i left 0)) /\ ((Znth i left 0) < 1073741824)))) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) < 1073741824)))) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : ((Zlength (right)) = n_pre)) ,
  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ ((-1) <= 29) ” 
  &&  “ (29 <= 29) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 1073741824) ” 
  &&  “ (GreedyMaskPrefixOptimal left right 29 0 ) ” 
  &&  “ (0 <= 29) ”
  &&  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre )
) \/
(
forall (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i left 0)) /\ ((Znth i left 0) < 1073741824)))) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) < 1073741824)))) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : ((Zlength (right)) = n_pre)) ,
  TT && emp 
|--
  “ (GreedyMaskPrefixOptimal left right 29 0 ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i left 0)) /\ ((Znth i left 0) < 1073741824)))) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) < 1073741824)))) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : ((Zlength (right)) = n_pre)) ,
  (GreedyMaskPrefixOptimal left right 29 0 )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i left 0)) /\ ((Znth i left 0) < 1073741824)))) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) < 1073741824)))) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : ((Zlength (right)) = n_pre)) ,
  forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i left 0)) /\ ((Znth i left 0) < 1073741824)))) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) < 1073741824)))) (PreH5 : (n_pre = (Zlength (left)))) (PreH6 : ((Zlength (right)) = n_pre)) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))
.

Definition solver_entail_wit_2 := 
(
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (PreH1 : (bit >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH7 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH8 : ((-1) <= bit)) (PreH9 : (bit <= 29)) (PreH10 : (0 <= ans)) (PreH11 : (ans < 1073741824)) (PreH12 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH13 : (0 <= bit)) ,
  ((( &( "cand" ) )) # UInt  |-> (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "ans" ) )) # UInt  |-> ans)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre )
|--
  “ (0 <= (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32)))) ” 
  &&  “ ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) < 1073741824) ” 
  &&  “ (ans <= UINT_MAX) ” 
  &&  “ (ans >= 0) ” 
  &&  “ (bit <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (bit >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (bit >= 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ ((-1) <= bit) ” 
  &&  “ (bit <= 29) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans < 1073741824) ” 
  &&  “ (GreedyMaskPrefixOptimal left right bit ans ) ” 
  &&  “ (0 <= bit) ”
  &&  ((( &( "cand" ) )) # UInt  |-> (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "ans" ) )) # UInt  |-> ans)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre )
) \/
(
forall (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (PreH1 : (ans <= UINT_MAX)) (PreH2 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) <= UINT_MAX)) (PreH3 : (ans >= 0)) (PreH4 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) >= 0)) (PreH5 : (bit <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (bit >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (bit >= 0)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (n_pre = (Zlength (left)))) (PreH13 : ((Zlength (right)) = n_pre)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH16 : ((-1) <= bit)) (PreH17 : (bit <= 29)) (PreH18 : (0 <= ans)) (PreH19 : (ans < 1073741824)) (PreH20 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH21 : (0 <= bit)) ,
  TT && emp 
|--
  “ ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) < 1073741824) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (PreH1 : (ans <= UINT_MAX)) (PreH2 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) <= UINT_MAX)) (PreH3 : (ans >= 0)) (PreH4 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) >= 0)) (PreH5 : (bit <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (bit >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (bit >= 0)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (n_pre = (Zlength (left)))) (PreH13 : ((Zlength (right)) = n_pre)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH16 : ((-1) <= bit)) (PreH17 : (bit <= 29)) (PreH18 : (0 <= ans)) (PreH19 : (ans < 1073741824)) (PreH20 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH21 : (0 <= bit)) ,
  ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) < 1073741824)
.

Definition solver_entail_wit_3_1 := 
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (MaskFeasible left right (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) ))) (PreH4 : ((retval = 0) -> ~((MaskFeasible left right (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) )))) (PreH5 : (0 <= (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))))) (PreH6 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) < 1073741824)) (PreH7 : (ans <= UINT_MAX)) (PreH8 : (ans >= 0)) (PreH9 : (bit <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (bit >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (bit >= 0)) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : (n_pre = (Zlength (left)))) (PreH17 : ((Zlength (right)) = n_pre)) (PreH18 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH20 : ((-1) <= bit)) (PreH21 : (bit <= 29)) (PreH22 : (0 <= ans)) (PreH23 : (ans < 1073741824)) (PreH24 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH25 : (0 <= bit)) (PreH26 : (retval <> 0)) ,
  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full_shape ka_pre n_pre )
  **  (UIntArray.full_shape kb_pre n_pre )
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ ((-1) <= (bit - 1 )) ” 
  &&  “ ((bit - 1 ) <= 29) ” 
  &&  “ (0 <= (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32)))) ” 
  &&  “ ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) < 1073741824) ” 
  &&  “ (GreedyMaskPrefixOptimal left right (bit - 1 ) (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) ) ” 
  &&  “ (0 <= (bit - 1 )) ”
  &&  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre ))
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ ((-1) <= (bit - 1 )) ” 
  &&  “ ((bit - 1 ) <= 29) ” 
  &&  “ (0 <= (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32)))) ” 
  &&  “ ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) < 1073741824) ” 
  &&  “ (GreedyMaskPrefixOptimal left right (bit - 1 ) (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) ) ” 
  &&  “ ((bit - 1 ) = (-1)) ”
  &&  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full_shape ka_pre n_pre )
  **  (UIntArray.full_shape kb_pre n_pre ))
.

Definition solver_entail_wit_3_2 := 
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (MaskFeasible left right (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) ))) (PreH4 : ((retval = 0) -> ~((MaskFeasible left right (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) )))) (PreH5 : (0 <= (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))))) (PreH6 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) < 1073741824)) (PreH7 : (ans <= UINT_MAX)) (PreH8 : (ans >= 0)) (PreH9 : (bit <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (bit >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (bit >= 0)) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : (n_pre = (Zlength (left)))) (PreH17 : ((Zlength (right)) = n_pre)) (PreH18 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH20 : ((-1) <= bit)) (PreH21 : (bit <= 29)) (PreH22 : (0 <= ans)) (PreH23 : (ans < 1073741824)) (PreH24 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH25 : (0 <= bit)) (PreH26 : (retval = 0)) ,
  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full_shape ka_pre n_pre )
  **  (UIntArray.full_shape kb_pre n_pre )
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ ((-1) <= (bit - 1 )) ” 
  &&  “ ((bit - 1 ) <= 29) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans < 1073741824) ” 
  &&  “ (GreedyMaskPrefixOptimal left right (bit - 1 ) ans ) ” 
  &&  “ (0 <= (bit - 1 )) ”
  &&  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre ))
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ ((-1) <= (bit - 1 )) ” 
  &&  “ ((bit - 1 ) <= 29) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans < 1073741824) ” 
  &&  “ (GreedyMaskPrefixOptimal left right (bit - 1 ) ans ) ” 
  &&  “ ((bit - 1 ) = (-1)) ”
  &&  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full_shape ka_pre n_pre )
  **  (UIntArray.full_shape kb_pre n_pre ))
.

Definition solver_return_wit_1 := 
(
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (PreH1 : (bit < 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH7 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH8 : ((-1) <= bit)) (PreH9 : (bit <= 29)) (PreH10 : (0 <= ans)) (PreH11 : (ans < 1073741824)) (PreH12 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH13 : (bit = (-1))) ,
  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full_shape ka_pre n_pre )
  **  (UIntArray.full_shape kb_pre n_pre )
|--
  “ (Spec left right ans ) ”
  &&  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.full_shape ka_pre n_pre )
  **  (UIntArray.full_shape kb_pre n_pre )
) \/
(
forall (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (PreH1 : (bit < 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH7 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH8 : ((-1) <= bit)) (PreH9 : (bit <= 29)) (PreH10 : (0 <= ans)) (PreH11 : (ans < 1073741824)) (PreH12 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH13 : (bit = (-1))) ,
  TT && emp 
|--
  “ (Spec left right ans ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (PreH1 : (bit < 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (left)))) (PreH5 : ((Zlength (right)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH7 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH8 : ((-1) <= bit)) (PreH9 : (bit <= 29)) (PreH10 : (0 <= ans)) (PreH11 : (ans < 1073741824)) (PreH12 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH13 : (bit = (-1))) ,
  (Spec left right ans )
.

Definition solver_partial_solve_wit_1_pure := 
(
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (PreH1 : (0 <= (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))))) (PreH2 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) < 1073741824)) (PreH3 : (ans <= UINT_MAX)) (PreH4 : (ans >= 0)) (PreH5 : (bit <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (bit >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (bit >= 0)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (n_pre = (Zlength (left)))) (PreH13 : ((Zlength (right)) = n_pre)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH16 : ((-1) <= bit)) (PreH17 : (bit <= 29)) (PreH18 : (0 <= ans)) (PreH19 : (ans < 1073741824)) (PreH20 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH21 : (0 <= bit)) ,
  ((( &( "cand" ) )) # UInt  |-> (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "ans" ) )) # UInt  |-> ans)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ (0 <= (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32)))) ” 
  &&  “ ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) < 1073741824) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) < 1073741824))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i left 0)) /\ ((Znth i left 0) < 1073741824))) ”
) \/
(
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (PreH1 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) <= UINT_MAX)) (PreH2 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) >= 0)) (PreH3 : (0 <= (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))))) (PreH4 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) < 1073741824)) (PreH5 : (ans <= UINT_MAX)) (PreH6 : (ans >= 0)) (PreH7 : (bit <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (bit >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (bit >= 0)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (n_pre = (Zlength (left)))) (PreH15 : ((Zlength (right)) = n_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH18 : ((-1) <= bit)) (PreH19 : (bit <= 29)) (PreH20 : (0 <= ans)) (PreH21 : (ans < 1073741824)) (PreH22 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH23 : (0 <= bit)) ,
  ((( &( "cand" ) )) # UInt  |-> (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "ans" ) )) # UInt  |-> ans)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre )
|--
  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i left 0)) /\ ((Znth i left 0) < 1073741824))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) < 1073741824))) ”
).

Definition solver_partial_solve_wit_1_pure_split_goal_1 := 
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (PreH1 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) <= UINT_MAX)) (PreH2 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) >= 0)) (PreH3 : (0 <= (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))))) (PreH4 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) < 1073741824)) (PreH5 : (ans <= UINT_MAX)) (PreH6 : (ans >= 0)) (PreH7 : (bit <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (bit >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (bit >= 0)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (n_pre = (Zlength (left)))) (PreH15 : ((Zlength (right)) = n_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH18 : ((-1) <= bit)) (PreH19 : (bit <= 29)) (PreH20 : (0 <= ans)) (PreH21 : (ans < 1073741824)) (PreH22 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH23 : (0 <= bit)) ,
  ((( &( "cand" ) )) # UInt  |-> (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "ans" ) )) # UInt  |-> ans)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre )
|--
  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i left 0)) /\ ((Znth i left 0) < 1073741824))) ”
.

Definition solver_partial_solve_wit_1_pure_split_goal_2 := 
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (PreH1 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) <= UINT_MAX)) (PreH2 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) >= 0)) (PreH3 : (0 <= (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))))) (PreH4 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) < 1073741824)) (PreH5 : (ans <= UINT_MAX)) (PreH6 : (ans >= 0)) (PreH7 : (bit <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (bit >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (bit >= 0)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (n_pre = (Zlength (left)))) (PreH15 : ((Zlength (right)) = n_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH18 : ((-1) <= bit)) (PreH19 : (bit <= 29)) (PreH20 : (0 <= ans)) (PreH21 : (ans < 1073741824)) (PreH22 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH23 : (0 <= bit)) ,
  ((( &( "cand" ) )) # UInt  |-> (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ka" ) )) # Ptr  |-> ka_pre)
  **  ((( &( "kb" ) )) # Ptr  |-> kb_pre)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "ans" ) )) # UInt  |-> ans)
  **  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre )
|--
  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) < 1073741824))) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (kb_pre: Z) (ka_pre: Z) (n_pre: Z) (b_pre: Z) (a_pre: Z) (right: (@list Z)) (left: (@list Z)) (ans: Z) (bit: Z) (PreH1 : (0 <= (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))))) (PreH2 : ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) < 1073741824)) (PreH3 : (ans <= UINT_MAX)) (PreH4 : (ans >= 0)) (PreH5 : (bit <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (bit >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (bit >= 0)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (n_pre = (Zlength (left)))) (PreH13 : ((Zlength (right)) = n_pre)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824)))) (PreH16 : ((-1) <= bit)) (PreH17 : (bit <= 29)) (PreH18 : (0 <= ans)) (PreH19 : (ans < 1073741824)) (PreH20 : (GreedyMaskPrefixOptimal left right bit ans )) (PreH21 : (0 <= bit)) ,
  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ (0 <= (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32)))) ” 
  &&  “ ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) < 1073741824) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 right 0)) /\ ((Znth i_2 right 0) < 1073741824))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i left 0)) /\ ((Znth i left 0) < 1073741824))) ” 
  &&  “ (0 <= (Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32)))) ” 
  &&  “ ((Z.lor ans (unsigned_last_nbits ((Z.shiftl 1 bit)) (32))) < 1073741824) ” 
  &&  “ (ans <= UINT_MAX) ” 
  &&  “ (ans >= 0) ” 
  &&  “ (bit <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (bit >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (bit >= 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (left))) ” 
  &&  “ ((Zlength (right)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j left 0)) /\ ((Znth j left 0) < 1073741824))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 right 0)) /\ ((Znth j_2 right 0) < 1073741824))) ” 
  &&  “ ((-1) <= bit) ” 
  &&  “ (bit <= 29) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans < 1073741824) ” 
  &&  “ (GreedyMaskPrefixOptimal left right bit ans ) ” 
  &&  “ (0 <= bit) ”
  &&  (UIntArray.full a_pre n_pre left )
  **  (UIntArray.full b_pre n_pre right )
  **  (UIntArray.undef_full ka_pre n_pre )
  **  (UIntArray.undef_full kb_pre n_pre )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_feasible_safety_wit_1 : feasible_safety_wit_1.
Axiom proof_of_feasible_safety_wit_2 : feasible_safety_wit_2.
Axiom proof_of_feasible_safety_wit_3 : feasible_safety_wit_3.
Axiom proof_of_feasible_safety_wit_4 : feasible_safety_wit_4.
Axiom proof_of_feasible_safety_wit_5 : feasible_safety_wit_5.
Axiom proof_of_feasible_safety_wit_6 : feasible_safety_wit_6.
Axiom proof_of_feasible_entail_wit_1 : feasible_entail_wit_1.
Axiom proof_of_feasible_entail_wit_2 : feasible_entail_wit_2.
Axiom proof_of_feasible_entail_wit_3 : feasible_entail_wit_3.
Axiom proof_of_feasible_entail_wit_4 : feasible_entail_wit_4.
Axiom proof_of_feasible_entail_wit_5 : feasible_entail_wit_5.
Axiom proof_of_feasible_entail_wit_6 : feasible_entail_wit_6.
Axiom proof_of_feasible_entail_wit_7 : feasible_entail_wit_7.
Axiom proof_of_feasible_return_wit_1 : feasible_return_wit_1.
Axiom proof_of_feasible_return_wit_2 : feasible_return_wit_2.
Axiom proof_of_feasible_partial_solve_wit_1 : feasible_partial_solve_wit_1.
Axiom proof_of_feasible_partial_solve_wit_2 : feasible_partial_solve_wit_2.
Axiom proof_of_feasible_partial_solve_wit_3 : feasible_partial_solve_wit_3.
Axiom proof_of_feasible_partial_solve_wit_4 : feasible_partial_solve_wit_4.
Axiom proof_of_feasible_partial_solve_wit_5_pure : feasible_partial_solve_wit_5_pure.
Axiom proof_of_feasible_partial_solve_wit_5 : feasible_partial_solve_wit_5.
Axiom proof_of_feasible_partial_solve_wit_6_pure : feasible_partial_solve_wit_6_pure.
Axiom proof_of_feasible_partial_solve_wit_6 : feasible_partial_solve_wit_6.
Axiom proof_of_feasible_partial_solve_wit_7 : feasible_partial_solve_wit_7.
Axiom proof_of_feasible_partial_solve_wit_8 : feasible_partial_solve_wit_8.
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
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.

End VC_Correct.
