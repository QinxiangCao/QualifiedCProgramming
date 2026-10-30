From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (PreH1 : (1 <= (Zlength (last_numbers)))) (PreH2 : ((Zlength (last_numbers)) <= 1000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (last_numbers)))) -> ((1 <= (Znth i last_numbers 0)) /\ ((Znth i last_numbers 0) <= (Zlength (last_numbers)))))) (PreH4 : (Pre last_numbers )) (PreH5 : (n_pre = (Zlength (last_numbers)))),
  ((( &( "total" ) )) # Int  |->_)
  **  ((( &( "depth" ) )) # Int  |-> 0)
  **  (IntArray.undef_full ( &( "stack" ) ) 1005 )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.undef_full flat_pre (n_pre * n_pre ) )
  **  (IntArray.undef_full lengths_pre n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (PreH1 : (1 <= (Zlength (last_numbers)))) (PreH2 : ((Zlength (last_numbers)) <= 1000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (last_numbers)))) -> ((1 <= (Znth i last_numbers 0)) /\ ((Znth i last_numbers 0) <= (Zlength (last_numbers)))))) (PreH4 : (Pre last_numbers )) (PreH5 : (n_pre = (Zlength (last_numbers)))),
  ((( &( "depth" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "stack" ) ) 1005 )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.undef_full flat_pre (n_pre * n_pre ) )
  **  (IntArray.undef_full lengths_pre n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (PreH1 : (1 <= (Zlength (last_numbers)))) (PreH2 : ((Zlength (last_numbers)) <= 1000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (last_numbers)))) -> ((1 <= (Znth i last_numbers 0)) /\ ((Znth i last_numbers 0) <= (Zlength (last_numbers)))))) (PreH4 : (Pre last_numbers )) (PreH5 : (n_pre = (Zlength (last_numbers)))),
  ((( &( "line" ) )) # Int  |->_)
  **  ((( &( "total" ) )) # Int  |-> 0)
  **  ((( &( "depth" ) )) # Int  |-> 0)
  **  (IntArray.undef_full ( &( "stack" ) ) 1005 )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.undef_full flat_pre (n_pre * n_pre ) )
  **  (IntArray.undef_full lengths_pre n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : (line < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH6 : (Pre last_numbers )) (PreH7 : (Spec last_numbers items )) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : (0 <= line)) (PreH10 : (line <= n_pre)) (PreH11 : (0 <= depth)) (PreH12 : (depth <= line)) (PreH13 : (depth = (Zlength (active)))) (PreH14 : (CurrentItem items line active )) (PreH15 : (BoundedItem n_pre active )) (PreH16 : (total = (Zlength (flat_data)))) (PreH17 : (0 <= total)) (PreH18 : (total <= (line * n_pre ))) (PreH19 : (FlatPrefix items line flat_data )) (PreH20 : (LengthsPrefix items line lengths_data )) (PreH21 : ((Zlength (cells)) = 1005)) (PreH22 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))),
  (IntArray.full values_pre n_pre last_numbers )
  **  ((( &( "x" ) )) # Int  |-> (Znth line last_numbers 0))
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "line" ) )) # Int  |-> line)
  **  ((( &( "depth" ) )) # Int  |-> depth)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : ((Znth line last_numbers 0) = 1)) (PreH2 : (line < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH7 : (Pre last_numbers )) (PreH8 : (Spec last_numbers items )) (PreH9 : ((Zlength (items)) = n_pre)) (PreH10 : (0 <= line)) (PreH11 : (line <= n_pre)) (PreH12 : (0 <= depth)) (PreH13 : (depth <= line)) (PreH14 : (depth = (Zlength (active)))) (PreH15 : (CurrentItem items line active )) (PreH16 : (BoundedItem n_pre active )) (PreH17 : (total = (Zlength (flat_data)))) (PreH18 : (0 <= total)) (PreH19 : (total <= (line * n_pre ))) (PreH20 : (FlatPrefix items line flat_data )) (PreH21 : (LengthsPrefix items line lengths_data )) (PreH22 : ((Zlength (cells)) = 1005)) (PreH23 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))),
  (IntArray.full values_pre n_pre last_numbers )
  **  ((( &( "x" ) )) # Int  |-> (Znth line last_numbers 0))
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "line" ) )) # Int  |-> line)
  **  ((( &( "depth" ) )) # Int  |-> depth)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : ((Znth line last_numbers 0) = 1)) (PreH2 : (line < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH7 : (Pre last_numbers )) (PreH8 : (Spec last_numbers items )) (PreH9 : ((Zlength (items)) = n_pre)) (PreH10 : (0 <= line)) (PreH11 : (line <= n_pre)) (PreH12 : (0 <= depth)) (PreH13 : (depth <= line)) (PreH14 : (depth = (Zlength (active)))) (PreH15 : (CurrentItem items line active )) (PreH16 : (BoundedItem n_pre active )) (PreH17 : (total = (Zlength (flat_data)))) (PreH18 : (0 <= total)) (PreH19 : (total <= (line * n_pre ))) (PreH20 : (FlatPrefix items line flat_data )) (PreH21 : (LengthsPrefix items line lengths_data )) (PreH22 : ((Zlength (cells)) = 1005)) (PreH23 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))),
  (IntArray.mixed_full ( &( "stack" ) ) 1005 (replace_Znth (depth) ((Some (1))) (cells)) )
  **  (IntArray.full values_pre n_pre last_numbers )
  **  ((( &( "x" ) )) # Int  |-> (Znth line last_numbers 0))
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "line" ) )) # Int  |-> line)
  **  ((( &( "depth" ) )) # Int  |-> depth)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ ((depth + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (depth + 1 )) ”
.

Definition solver_safety_wit_7 :=
(
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (target: (@list Z)) (x: Z) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : (depth <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH6 : (Pre last_numbers )) (PreH7 : (Spec last_numbers items )) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : (0 < line)) (PreH10 : (line < n_pre)) (PreH11 : (x = (Znth (line) (last_numbers) (0)))) (PreH12 : (x <> 1)) (PreH13 : (target = (Znth (line) (items) ((@nil Z))))) (PreH14 : (1 <= depth)) (PreH15 : (depth <= line)) (PreH16 : (depth = (Zlength (active)))) (PreH17 : (PopTarget active target x )) (PreH18 : (BoundedItem n_pre active )) (PreH19 : (total = (Zlength (flat_data)))) (PreH20 : (0 <= total)) (PreH21 : (total <= (line * n_pre ))) (PreH22 : (FlatPrefix items line flat_data )) (PreH23 : (LengthsPrefix items line lengths_data )) (PreH24 : ((Zlength (cells)) = 1005)) (PreH25 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))) (PreH26 : ((Znth (depth - 1 ) cells __default__App_option_Z) = (Some ((Znth (depth - 1 ) active 0))))),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "line" ) )) # Int  |-> line)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "depth" ) )) # Int  |-> depth)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ (((Znth (depth - 1 ) active 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (depth - 1 ) active 0) + 1 )) ”
) \/
(
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (target: (@list Z)) (x: Z) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : (depth <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH6 : (Pre last_numbers )) (PreH7 : (Spec last_numbers items )) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : (0 < line)) (PreH10 : (line < n_pre)) (PreH11 : (x = (Znth (line) (last_numbers) (0)))) (PreH12 : (x <> 1)) (PreH13 : (target = (Znth (line) (items) ((@nil Z))))) (PreH14 : (1 <= depth)) (PreH15 : (depth <= line)) (PreH16 : (depth = (Zlength (active)))) (PreH17 : (PopTarget active target x )) (PreH18 : (BoundedItem n_pre active )) (PreH19 : (total = (Zlength (flat_data)))) (PreH20 : (0 <= total)) (PreH21 : (total <= (line * n_pre ))) (PreH22 : (FlatPrefix items line flat_data )) (PreH23 : (LengthsPrefix items line lengths_data )) (PreH24 : ((Zlength (cells)) = 1005)) (PreH25 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))) (PreH26 : ((Znth (depth - 1 ) cells __default__App_option_Z) = (Some ((Znth (depth - 1 ) active 0))))),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "line" ) )) # Int  |-> line)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "depth" ) )) # Int  |-> depth)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ (((Znth (depth - 1 ) active 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (depth - 1 ) active 0) + 1 )) ”
).

Definition solver_safety_wit_7_split_goal_1 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (target: (@list Z)) (x: Z) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : (depth <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH6 : (Pre last_numbers )) (PreH7 : (Spec last_numbers items )) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : (0 < line)) (PreH10 : (line < n_pre)) (PreH11 : (x = (Znth (line) (last_numbers) (0)))) (PreH12 : (x <> 1)) (PreH13 : (target = (Znth (line) (items) ((@nil Z))))) (PreH14 : (1 <= depth)) (PreH15 : (depth <= line)) (PreH16 : (depth = (Zlength (active)))) (PreH17 : (PopTarget active target x )) (PreH18 : (BoundedItem n_pre active )) (PreH19 : (total = (Zlength (flat_data)))) (PreH20 : (0 <= total)) (PreH21 : (total <= (line * n_pre ))) (PreH22 : (FlatPrefix items line flat_data )) (PreH23 : (LengthsPrefix items line lengths_data )) (PreH24 : ((Zlength (cells)) = 1005)) (PreH25 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))) (PreH26 : ((Znth (depth - 1 ) cells __default__App_option_Z) = (Some ((Znth (depth - 1 ) active 0))))),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "line" ) )) # Int  |-> line)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "depth" ) )) # Int  |-> depth)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ (((Znth (depth - 1 ) active 0) + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_7_split_goal_2 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (target: (@list Z)) (x: Z) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : (depth <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH6 : (Pre last_numbers )) (PreH7 : (Spec last_numbers items )) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : (0 < line)) (PreH10 : (line < n_pre)) (PreH11 : (x = (Znth (line) (last_numbers) (0)))) (PreH12 : (x <> 1)) (PreH13 : (target = (Znth (line) (items) ((@nil Z))))) (PreH14 : (1 <= depth)) (PreH15 : (depth <= line)) (PreH16 : (depth = (Zlength (active)))) (PreH17 : (PopTarget active target x )) (PreH18 : (BoundedItem n_pre active )) (PreH19 : (total = (Zlength (flat_data)))) (PreH20 : (0 <= total)) (PreH21 : (total <= (line * n_pre ))) (PreH22 : (FlatPrefix items line flat_data )) (PreH23 : (LengthsPrefix items line lengths_data )) (PreH24 : ((Zlength (cells)) = 1005)) (PreH25 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))) (PreH26 : ((Znth (depth - 1 ) cells __default__App_option_Z) = (Some ((Znth (depth - 1 ) active 0))))),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "line" ) )) # Int  |-> line)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "depth" ) )) # Int  |-> depth)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ ((INT_MIN) <= ((Znth (depth - 1 ) active 0) + 1 )) ”
.

Definition solver_safety_wit_8 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (target: (@list Z)) (x: Z) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : (depth <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH6 : (Pre last_numbers )) (PreH7 : (Spec last_numbers items )) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : (0 < line)) (PreH10 : (line < n_pre)) (PreH11 : (x = (Znth (line) (last_numbers) (0)))) (PreH12 : (x <> 1)) (PreH13 : (target = (Znth (line) (items) ((@nil Z))))) (PreH14 : (1 <= depth)) (PreH15 : (depth <= line)) (PreH16 : (depth = (Zlength (active)))) (PreH17 : (PopTarget active target x )) (PreH18 : (BoundedItem n_pre active )) (PreH19 : (total = (Zlength (flat_data)))) (PreH20 : (0 <= total)) (PreH21 : (total <= (line * n_pre ))) (PreH22 : (FlatPrefix items line flat_data )) (PreH23 : (LengthsPrefix items line lengths_data )) (PreH24 : ((Zlength (cells)) = 1005)) (PreH25 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))) (PreH26 : ((Znth (depth - 1 ) cells __default__App_option_Z) = (Some ((Znth (depth - 1 ) active 0))))),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "line" ) )) # Int  |-> line)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "depth" ) )) # Int  |-> depth)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ ((depth - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (depth - 1 )) ”
.

Definition solver_safety_wit_9 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (target: (@list Z)) (x: Z) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : (depth <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH6 : (Pre last_numbers )) (PreH7 : (Spec last_numbers items )) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : (0 < line)) (PreH10 : (line < n_pre)) (PreH11 : (x = (Znth (line) (last_numbers) (0)))) (PreH12 : (x <> 1)) (PreH13 : (target = (Znth (line) (items) ((@nil Z))))) (PreH14 : (1 <= depth)) (PreH15 : (depth <= line)) (PreH16 : (depth = (Zlength (active)))) (PreH17 : (PopTarget active target x )) (PreH18 : (BoundedItem n_pre active )) (PreH19 : (total = (Zlength (flat_data)))) (PreH20 : (0 <= total)) (PreH21 : (total <= (line * n_pre ))) (PreH22 : (FlatPrefix items line flat_data )) (PreH23 : (LengthsPrefix items line lengths_data )) (PreH24 : ((Zlength (cells)) = 1005)) (PreH25 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))) (PreH26 : ((Znth (depth - 1 ) cells __default__App_option_Z) = (Some ((Znth (depth - 1 ) active 0))))),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "line" ) )) # Int  |-> line)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "depth" ) )) # Int  |-> depth)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (target: (@list Z)) (x: Z) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : (depth <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH6 : (Pre last_numbers )) (PreH7 : (Spec last_numbers items )) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : (0 < line)) (PreH10 : (line < n_pre)) (PreH11 : (x = (Znth (line) (last_numbers) (0)))) (PreH12 : (x <> 1)) (PreH13 : (target = (Znth (line) (items) ((@nil Z))))) (PreH14 : (1 <= depth)) (PreH15 : (depth <= line)) (PreH16 : (depth = (Zlength (active)))) (PreH17 : (PopTarget active target x )) (PreH18 : (BoundedItem n_pre active )) (PreH19 : (total = (Zlength (flat_data)))) (PreH20 : (0 <= total)) (PreH21 : (total <= (line * n_pre ))) (PreH22 : (FlatPrefix items line flat_data )) (PreH23 : (LengthsPrefix items line lengths_data )) (PreH24 : ((Zlength (cells)) = 1005)) (PreH25 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))) (PreH26 : ((Znth (depth - 1 ) cells __default__App_option_Z) = (Some ((Znth (depth - 1 ) active 0))))),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "line" ) )) # Int  |-> line)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "depth" ) )) # Int  |-> depth)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_11 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (target: (@list Z)) (x: Z) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : (depth = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH6 : (Pre last_numbers )) (PreH7 : (Spec last_numbers items )) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : (0 < line)) (PreH10 : (line < n_pre)) (PreH11 : (x = (Znth (line) (last_numbers) (0)))) (PreH12 : (x <> 1)) (PreH13 : (target = (Znth (line) (items) ((@nil Z))))) (PreH14 : (1 <= depth)) (PreH15 : (depth <= line)) (PreH16 : (depth = (Zlength (active)))) (PreH17 : (PopTarget active target x )) (PreH18 : (BoundedItem n_pre active )) (PreH19 : (total = (Zlength (flat_data)))) (PreH20 : (0 <= total)) (PreH21 : (total <= (line * n_pre ))) (PreH22 : (FlatPrefix items line flat_data )) (PreH23 : (LengthsPrefix items line lengths_data )) (PreH24 : ((Zlength (cells)) = 1005)) (PreH25 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))) (PreH26 : ((Znth (depth - 1 ) cells __default__App_option_Z) = (Some ((Znth (depth - 1 ) active 0))))),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "line" ) )) # Int  |-> line)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "depth" ) )) # Int  |-> depth)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ False ”
.

Definition solver_safety_wit_12 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (target: (@list Z)) (x: Z) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : (((Znth (depth - 1 ) active 0) + 1 ) <> x)) (PreH2 : (depth <> 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH7 : (Pre last_numbers )) (PreH8 : (Spec last_numbers items )) (PreH9 : ((Zlength (items)) = n_pre)) (PreH10 : (0 < line)) (PreH11 : (line < n_pre)) (PreH12 : (x = (Znth (line) (last_numbers) (0)))) (PreH13 : (x <> 1)) (PreH14 : (target = (Znth (line) (items) ((@nil Z))))) (PreH15 : (1 <= depth)) (PreH16 : (depth <= line)) (PreH17 : (depth = (Zlength (active)))) (PreH18 : (PopTarget active target x )) (PreH19 : (BoundedItem n_pre active )) (PreH20 : (total = (Zlength (flat_data)))) (PreH21 : (0 <= total)) (PreH22 : (total <= (line * n_pre ))) (PreH23 : (FlatPrefix items line flat_data )) (PreH24 : (LengthsPrefix items line lengths_data )) (PreH25 : ((Zlength (cells)) = 1005)) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))) (PreH27 : ((Znth (depth - 1 ) cells __default__App_option_Z) = (Some ((Znth (depth - 1 ) active 0))))),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "line" ) )) # Int  |-> line)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "depth" ) )) # Int  |-> depth)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ ((depth - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (depth - 1 )) ”
.

Definition solver_safety_wit_13 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (target: (@list Z)) (x: Z) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : (((Znth (depth - 1 ) active 0) + 1 ) = x)) (PreH2 : (depth <> 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH7 : (Pre last_numbers )) (PreH8 : (Spec last_numbers items )) (PreH9 : ((Zlength (items)) = n_pre)) (PreH10 : (0 < line)) (PreH11 : (line < n_pre)) (PreH12 : (x = (Znth (line) (last_numbers) (0)))) (PreH13 : (x <> 1)) (PreH14 : (target = (Znth (line) (items) ((@nil Z))))) (PreH15 : (1 <= depth)) (PreH16 : (depth <= line)) (PreH17 : (depth = (Zlength (active)))) (PreH18 : (PopTarget active target x )) (PreH19 : (BoundedItem n_pre active )) (PreH20 : (total = (Zlength (flat_data)))) (PreH21 : (0 <= total)) (PreH22 : (total <= (line * n_pre ))) (PreH23 : (FlatPrefix items line flat_data )) (PreH24 : (LengthsPrefix items line lengths_data )) (PreH25 : ((Zlength (cells)) = 1005)) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))) (PreH27 : ((Znth (depth - 1 ) cells __default__App_option_Z) = (Some ((Znth (depth - 1 ) active 0))))),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "line" ) )) # Int  |-> line)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "depth" ) )) # Int  |-> depth)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ ((depth - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (depth - 1 )) ”
.

Definition solver_safety_wit_14 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (target: (@list Z)) (x: Z) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : (((Znth (depth - 1 ) active 0) + 1 ) = x)) (PreH2 : (depth <> 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH7 : (Pre last_numbers )) (PreH8 : (Spec last_numbers items )) (PreH9 : ((Zlength (items)) = n_pre)) (PreH10 : (0 < line)) (PreH11 : (line < n_pre)) (PreH12 : (x = (Znth (line) (last_numbers) (0)))) (PreH13 : (x <> 1)) (PreH14 : (target = (Znth (line) (items) ((@nil Z))))) (PreH15 : (1 <= depth)) (PreH16 : (depth <= line)) (PreH17 : (depth = (Zlength (active)))) (PreH18 : (PopTarget active target x )) (PreH19 : (BoundedItem n_pre active )) (PreH20 : (total = (Zlength (flat_data)))) (PreH21 : (0 <= total)) (PreH22 : (total <= (line * n_pre ))) (PreH23 : (FlatPrefix items line flat_data )) (PreH24 : (LengthsPrefix items line lengths_data )) (PreH25 : ((Zlength (cells)) = 1005)) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))) (PreH27 : ((Znth (depth - 1 ) cells __default__App_option_Z) = (Some ((Znth (depth - 1 ) active 0))))),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "line" ) )) # Int  |-> line)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "depth" ) )) # Int  |-> depth)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_15 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (items: (@list (@list Z))) (cells: (@list (@option Z))) (active: (@list Z)) (flat_data: (@list Z)) (lengths_data: (@list Z)) (line: Z) (depth: Z) (total: Z) __default__App_option_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH5 : (Pre last_numbers )) (PreH6 : (Spec last_numbers items )) (PreH7 : ((Zlength (items)) = n_pre)) (PreH8 : (0 <= line)) (PreH9 : (line < n_pre)) (PreH10 : (active = (Znth (line) (items) ((@nil Z))))) (PreH11 : (1 <= depth)) (PreH12 : (depth <= (line + 1 ))) (PreH13 : (depth = (Zlength (active)))) (PreH14 : (BoundedItem n_pre active )) (PreH15 : (total = (Zlength (flat_data)))) (PreH16 : (0 <= total)) (PreH17 : (total <= (line * n_pre ))) (PreH18 : (FlatPrefix items line flat_data )) (PreH19 : (LengthsPrefix items line lengths_data )) (PreH20 : ((Zlength (cells)) = 1005)) (PreH21 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))),
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.seg lengths_pre 0 (line + 1 ) (app (lengths_data) ((cons (depth) ((@nil Z))))) )
  **  (IntArray.undef_seg lengths_pre (line + 1 ) n_pre )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "line" ) )) # Int  |-> line)
  **  ((( &( "depth" ) )) # Int  |-> depth)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "x" ) )) # Int  |->_)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_16 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (items: (@list (@list Z))) (cells: (@list (@option Z))) (active: (@list Z)) (flat_before: (@list Z)) (flat_data: (@list Z)) (lengths_data: (@list Z)) (line: Z) (depth: Z) (i: Z) (total: Z) __default__App_option_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH5 : (Pre last_numbers )) (PreH6 : (Spec last_numbers items )) (PreH7 : ((Zlength (items)) = n_pre)) (PreH8 : (0 <= line)) (PreH9 : (line < n_pre)) (PreH10 : (active = (Znth (line) (items) ((@nil Z))))) (PreH11 : (1 <= depth)) (PreH12 : (depth <= (line + 1 ))) (PreH13 : ((line + 1 ) <= n_pre)) (PreH14 : (depth = (Zlength (active)))) (PreH15 : (BoundedItem n_pre active )) (PreH16 : (0 <= i)) (PreH17 : (i < depth)) (PreH18 : (FlatPrefix items line flat_before )) (PreH19 : (flat_data = (app (flat_before) ((sublist (0) (i) (active)))))) (PreH20 : (total = (Zlength (flat_data)))) (PreH21 : (0 <= total)) (PreH22 : ((total + (depth - i ) ) <= ((line + 1 ) * n_pre ))) (PreH23 : (((line + 1 ) * n_pre ) <= (n_pre * n_pre ))) (PreH24 : (LengthsPrefix items (line + 1 ) lengths_data )) (PreH25 : ((Zlength (cells)) = 1005)) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))) (PreH27 : ((Znth i cells __default__App_option_Z) = (Some ((Znth i active 0))))),
  (IntArray.seg flat_pre 0 (total + 1 ) (app (flat_data) ((cons ((Znth i active 0)) ((@nil Z))))) )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
  **  (IntArray.undef_seg flat_pre (total + 1 ) (n_pre * n_pre ) )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "line" ) )) # Int  |-> line)
  **  ((( &( "depth" ) )) # Int  |-> depth)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "x" ) )) # Int  |->_)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.seg lengths_pre 0 (line + 1 ) lengths_data )
  **  (IntArray.undef_seg lengths_pre (line + 1 ) n_pre )
|--
  “ ((total + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (total + 1 )) ”
.

Definition solver_safety_wit_17 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (items: (@list (@list Z))) (cells: (@list (@option Z))) (active: (@list Z)) (flat_before: (@list Z)) (flat_data: (@list Z)) (lengths_data: (@list Z)) (line: Z) (depth: Z) (i: Z) (total: Z) __default__App_option_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH5 : (Pre last_numbers )) (PreH6 : (Spec last_numbers items )) (PreH7 : ((Zlength (items)) = n_pre)) (PreH8 : (0 <= line)) (PreH9 : (line < n_pre)) (PreH10 : (active = (Znth (line) (items) ((@nil Z))))) (PreH11 : (1 <= depth)) (PreH12 : (depth <= (line + 1 ))) (PreH13 : ((line + 1 ) <= n_pre)) (PreH14 : (depth = (Zlength (active)))) (PreH15 : (BoundedItem n_pre active )) (PreH16 : (0 <= i)) (PreH17 : (i < depth)) (PreH18 : (FlatPrefix items line flat_before )) (PreH19 : (flat_data = (app (flat_before) ((sublist (0) (i) (active)))))) (PreH20 : (total = (Zlength (flat_data)))) (PreH21 : (0 <= total)) (PreH22 : ((total + (depth - i ) ) <= ((line + 1 ) * n_pre ))) (PreH23 : (((line + 1 ) * n_pre ) <= (n_pre * n_pre ))) (PreH24 : (LengthsPrefix items (line + 1 ) lengths_data )) (PreH25 : ((Zlength (cells)) = 1005)) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))) (PreH27 : ((Znth i cells __default__App_option_Z) = (Some ((Znth i active 0))))),
  (IntArray.seg flat_pre 0 (total + 1 ) (app (flat_data) ((cons ((Znth i active 0)) ((@nil Z))))) )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
  **  (IntArray.undef_seg flat_pre (total + 1 ) (n_pre * n_pre ) )
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "line" ) )) # Int  |-> line)
  **  ((( &( "depth" ) )) # Int  |-> depth)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> (total + 1 ))
  **  ((( &( "x" ) )) # Int  |->_)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.seg lengths_pre 0 (line + 1 ) lengths_data )
  **  (IntArray.undef_seg lengths_pre (line + 1 ) n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_18 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (total: Z) (flat_data: (@list Z)) (flat_before: (@list Z)) (i: Z) (depth: Z) (active: (@list Z)) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : (i >= depth)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH6 : (Pre last_numbers )) (PreH7 : (Spec last_numbers items )) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : (0 <= line)) (PreH10 : (line < n_pre)) (PreH11 : (active = (Znth (line) (items) ((@nil Z))))) (PreH12 : (1 <= depth)) (PreH13 : (depth <= (line + 1 ))) (PreH14 : ((line + 1 ) <= n_pre)) (PreH15 : (depth = (Zlength (active)))) (PreH16 : (BoundedItem n_pre active )) (PreH17 : (0 <= i)) (PreH18 : (i <= depth)) (PreH19 : (FlatPrefix items line flat_before )) (PreH20 : (flat_data = (app (flat_before) ((sublist (0) (i) (active)))))) (PreH21 : (total = (Zlength (flat_data)))) (PreH22 : (0 <= total)) (PreH23 : ((total + (depth - i ) ) <= ((line + 1 ) * n_pre ))) (PreH24 : (((line + 1 ) * n_pre ) <= (n_pre * n_pre ))) (PreH25 : (LengthsPrefix items (line + 1 ) lengths_data )) (PreH26 : ((Zlength (cells)) = 1005)) (PreH27 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))),
  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flat" ) )) # Ptr  |-> flat_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "line" ) )) # Int  |-> line)
  **  ((( &( "depth" ) )) # Int  |-> depth)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 (line + 1 ) lengths_data )
  **  (IntArray.undef_seg lengths_pre (line + 1 ) n_pre )
|--
  “ ((line + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (line + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) __default__App_option_Z (PreH1 : (1 <= (Zlength (last_numbers)))) (PreH2 : ((Zlength (last_numbers)) <= 1000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (last_numbers)))) -> ((1 <= (Znth i last_numbers 0)) /\ ((Znth i last_numbers 0) <= (Zlength (last_numbers)))))) (PreH4 : (Pre last_numbers )) (PreH5 : (n_pre = (Zlength (last_numbers)))),
  (IntArray.undef_full ( &( "stack" ) ) 1005 )
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.undef_full flat_pre (n_pre * n_pre ) )
  **  (IntArray.undef_full lengths_pre n_pre )
|--
  EX (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (active: (@list Z)) (items: (@list (@list Z))),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 = (Zlength (active))) ”
  &&  “ (CurrentItem items 0 active ) ”
  &&  “ (BoundedItem n_pre active ) ”
  &&  “ (0 = (Zlength (flat_data))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (0 * n_pre )) ”
  &&  “ (FlatPrefix items 0 flat_data ) ”
  &&  “ (LengthsPrefix items 0 lengths_data ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < 0)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
  **  (IntArray.seg flat_pre 0 0 flat_data )
  **  (IntArray.undef_seg flat_pre 0 (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 0 lengths_data )
  **  (IntArray.undef_seg lengths_pre 0 n_pre )
) \/
(
forall (last_numbers: (@list Z)) (n_pre: Z) __default__App_option_Z (PreH1 : (1 <= (Zlength (last_numbers)))) (PreH2 : ((Zlength (last_numbers)) <= 1000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (last_numbers)))) -> ((1 <= (Znth i last_numbers 0)) /\ ((Znth i last_numbers 0) <= (Zlength (last_numbers)))))) (PreH4 : (Pre last_numbers )) (PreH5 : (n_pre = (Zlength (last_numbers)))),
  (IntArray.undef_full ( &( "stack" ) ) 1005 )
|--
  EX (cells: (@list (@option Z))) (active: (@list Z)) (items: (@list (@list Z))),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 = (Zlength (active))) ”
  &&  “ (CurrentItem items 0 active ) ”
  &&  “ (BoundedItem n_pre active ) ”
  &&  “ (0 = (Zlength ((@nil Z)))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (0 * n_pre )) ”
  &&  “ (FlatPrefix items 0 (@nil Z) ) ”
  &&  “ (LengthsPrefix items 0 (@nil Z) ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < 0)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
).

Definition solver_entail_wit_2 :=
(
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells_2: (@list (@option Z))) (lengths_data_2: (@list Z)) (flat_data_2: (@list Z)) (total: Z) (active_2: (@list Z)) (depth: Z) (line: Z) (items_2: (@list (@list Z))) __default__App_option_Z (PreH1 : ((Znth line last_numbers 0) <> 1)) (PreH2 : (line < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) (0))) /\ ((Znth (k_3) (last_numbers) (0)) <= n_pre)))) (PreH7 : (Pre last_numbers )) (PreH8 : (Spec last_numbers items_2 )) (PreH9 : ((Zlength (items_2)) = n_pre)) (PreH10 : (0 <= line)) (PreH11 : (line <= n_pre)) (PreH12 : (0 <= depth)) (PreH13 : (depth <= line)) (PreH14 : (depth = (Zlength (active_2)))) (PreH15 : (CurrentItem items_2 line active_2 )) (PreH16 : (BoundedItem n_pre active_2 )) (PreH17 : (total = (Zlength (flat_data_2)))) (PreH18 : (0 <= total)) (PreH19 : (total <= (line * n_pre ))) (PreH20 : (FlatPrefix items_2 line flat_data_2 )) (PreH21 : (LengthsPrefix items_2 line lengths_data_2 )) (PreH22 : ((Zlength (cells_2)) = 1005)) (PreH23 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 0)))))),
  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells_2 )
  **  (IntArray.seg flat_pre 0 total flat_data_2 )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data_2 )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  EX (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (active: (@list Z)) (target: (@list Z)) (items: (@list (@list Z))),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 < line) ”
  &&  “ (line < n_pre) ”
  &&  “ ((Znth line last_numbers 0) = (Znth (line) (last_numbers) (0))) ”
  &&  “ ((Znth line last_numbers 0) <> 1) ”
  &&  “ (target = (Znth (line) (items) ((@nil Z)))) ”
  &&  “ (1 <= depth) ”
  &&  “ (depth <= line) ”
  &&  “ (depth = (Zlength (active))) ”
  &&  “ (PopTarget active target (Znth line last_numbers 0) ) ”
  &&  “ (BoundedItem n_pre active ) ”
  &&  “ (total = (Zlength (flat_data))) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= (line * n_pre )) ”
  &&  “ (FlatPrefix items line flat_data ) ”
  &&  “ (LengthsPrefix items line lengths_data ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  “ ((Znth (depth - 1 ) cells __default__App_option_Z) = (Some ((Znth (depth - 1 ) active 0)))) ”
  &&  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
) \/
(
forall (last_numbers: (@list Z)) (n_pre: Z) (cells_2: (@list (@option Z))) (lengths_data_2: (@list Z)) (flat_data_2: (@list Z)) (total: Z) (active_2: (@list Z)) (depth: Z) (line: Z) (items_2: (@list (@list Z))) __default__App_option_Z (PreH1 : ((Znth line last_numbers 0) <> 1)) (PreH2 : (line < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) (0))) /\ ((Znth (k_3) (last_numbers) (0)) <= n_pre)))) (PreH7 : (Pre last_numbers )) (PreH8 : (Spec last_numbers items_2 )) (PreH9 : ((Zlength (items_2)) = n_pre)) (PreH10 : (0 <= line)) (PreH11 : (line <= n_pre)) (PreH12 : (0 <= depth)) (PreH13 : (depth <= line)) (PreH14 : (depth = (Zlength (active_2)))) (PreH15 : (CurrentItem items_2 line active_2 )) (PreH16 : (BoundedItem n_pre active_2 )) (PreH17 : (total = (Zlength (flat_data_2)))) (PreH18 : (0 <= total)) (PreH19 : (total <= (line * n_pre ))) (PreH20 : (FlatPrefix items_2 line flat_data_2 )) (PreH21 : (LengthsPrefix items_2 line lengths_data_2 )) (PreH22 : ((Zlength (cells_2)) = 1005)) (PreH23 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 0)))))),
  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells_2 )
|--
  EX (cells: (@list (@option Z))) (active: (@list Z)) (items: (@list (@list Z))),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 < line) ”
  &&  “ (line < n_pre) ”
  &&  “ ((Znth line last_numbers 0) = (Znth (line) (last_numbers) (0))) ”
  &&  “ ((Znth line last_numbers 0) <> 1) ”
  &&  “ (1 <= depth) ”
  &&  “ (depth <= line) ”
  &&  “ (depth = (Zlength (active))) ”
  &&  “ (PopTarget active (Znth (line) (items) ((@nil Z))) (Znth line last_numbers 0) ) ”
  &&  “ (BoundedItem n_pre active ) ”
  &&  “ (total = (Zlength (flat_data_2))) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= (line * n_pre )) ”
  &&  “ (FlatPrefix items line flat_data_2 ) ”
  &&  “ (LengthsPrefix items line lengths_data_2 ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  “ ((Znth (depth - 1 ) cells __default__App_option_Z) = (Some ((Znth (depth - 1 ) active 0)))) ”
  &&  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells )
).

Definition solver_entail_wit_3_1 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (target: (@list Z)) (x: Z) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : (depth = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH6 : (Pre last_numbers )) (PreH7 : (Spec last_numbers items )) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : (0 < line)) (PreH10 : (line < n_pre)) (PreH11 : (x = (Znth (line) (last_numbers) (0)))) (PreH12 : (x <> 1)) (PreH13 : (target = (Znth (line) (items) ((@nil Z))))) (PreH14 : (1 <= depth)) (PreH15 : (depth <= line)) (PreH16 : (depth = (Zlength (active)))) (PreH17 : (PopTarget active target x )) (PreH18 : (BoundedItem n_pre active )) (PreH19 : (total = (Zlength (flat_data)))) (PreH20 : (0 <= total)) (PreH21 : (total <= (line * n_pre ))) (PreH22 : (FlatPrefix items line flat_data )) (PreH23 : (LengthsPrefix items line lengths_data )) (PreH24 : ((Zlength (cells)) = 1005)) (PreH25 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))) (PreH26 : ((Znth (depth - 1 ) cells __default__App_option_Z) = (Some ((Znth (depth - 1 ) active 0))))),
  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ (((Znth (depth - 1 ) active 0) + 1 ) = x) ”
  &&  “ (depth <> 0) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 < line) ”
  &&  “ (line < n_pre) ”
  &&  “ (x = (Znth (line) (last_numbers) (0))) ”
  &&  “ (x <> 1) ”
  &&  “ (target = (Znth (line) (items) ((@nil Z)))) ”
  &&  “ (1 <= depth) ”
  &&  “ (depth <= line) ”
  &&  “ (depth = (Zlength (active))) ”
  &&  “ (PopTarget active target x ) ”
  &&  “ (BoundedItem n_pre active ) ”
  &&  “ (total = (Zlength (flat_data))) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= (line * n_pre )) ”
  &&  “ (FlatPrefix items line flat_data ) ”
  &&  “ (LengthsPrefix items line lengths_data ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  “ ((Znth (depth - 1 ) cells __default__App_option_Z) = (Some ((Znth (depth - 1 ) active 0)))) ”
  &&  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
.

Definition solver_entail_wit_3_2 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (target: (@list Z)) (x: Z) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : (((Znth (depth - 1 ) active 0) + 1 ) = x)) (PreH2 : (depth <> 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH7 : (Pre last_numbers )) (PreH8 : (Spec last_numbers items )) (PreH9 : ((Zlength (items)) = n_pre)) (PreH10 : (0 < line)) (PreH11 : (line < n_pre)) (PreH12 : (x = (Znth (line) (last_numbers) (0)))) (PreH13 : (x <> 1)) (PreH14 : (target = (Znth (line) (items) ((@nil Z))))) (PreH15 : (1 <= depth)) (PreH16 : (depth <= line)) (PreH17 : (depth = (Zlength (active)))) (PreH18 : (PopTarget active target x )) (PreH19 : (BoundedItem n_pre active )) (PreH20 : (total = (Zlength (flat_data)))) (PreH21 : (0 <= total)) (PreH22 : (total <= (line * n_pre ))) (PreH23 : (FlatPrefix items line flat_data )) (PreH24 : (LengthsPrefix items line lengths_data )) (PreH25 : ((Zlength (cells)) = 1005)) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))) (PreH27 : ((Znth (depth - 1 ) cells __default__App_option_Z) = (Some ((Znth (depth - 1 ) active 0))))),
  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ (((Znth (depth - 1 ) active 0) + 1 ) = x) ”
  &&  “ (depth <> 0) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 < line) ”
  &&  “ (line < n_pre) ”
  &&  “ (x = (Znth (line) (last_numbers) (0))) ”
  &&  “ (x <> 1) ”
  &&  “ (target = (Znth (line) (items) ((@nil Z)))) ”
  &&  “ (1 <= depth) ”
  &&  “ (depth <= line) ”
  &&  “ (depth = (Zlength (active))) ”
  &&  “ (PopTarget active target x ) ”
  &&  “ (BoundedItem n_pre active ) ”
  &&  “ (total = (Zlength (flat_data))) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= (line * n_pre )) ”
  &&  “ (FlatPrefix items line flat_data ) ”
  &&  “ (LengthsPrefix items line lengths_data ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  “ ((Znth (depth - 1 ) cells __default__App_option_Z) = (Some ((Znth (depth - 1 ) active 0)))) ”
  &&  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
.

Definition solver_entail_wit_4 :=
(
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells_2: (@list (@option Z))) (lengths_data_2: (@list Z)) (flat_data_2: (@list Z)) (total: Z) (active_2: (@list Z)) (depth: Z) (target_2: (@list Z)) (x: Z) (line: Z) (items_2: (@list (@list Z))) __default__App_option_Z (PreH1 : (((Znth (depth - 1 ) active_2 0) + 1 ) <> x)) (PreH2 : (depth <> 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH7 : (Pre last_numbers )) (PreH8 : (Spec last_numbers items_2 )) (PreH9 : ((Zlength (items_2)) = n_pre)) (PreH10 : (0 < line)) (PreH11 : (line < n_pre)) (PreH12 : (x = (Znth (line) (last_numbers) (0)))) (PreH13 : (x <> 1)) (PreH14 : (target_2 = (Znth (line) (items_2) ((@nil Z))))) (PreH15 : (1 <= depth)) (PreH16 : (depth <= line)) (PreH17 : (depth = (Zlength (active_2)))) (PreH18 : (PopTarget active_2 target_2 x )) (PreH19 : (BoundedItem n_pre active_2 )) (PreH20 : (total = (Zlength (flat_data_2)))) (PreH21 : (0 <= total)) (PreH22 : (total <= (line * n_pre ))) (PreH23 : (FlatPrefix items_2 line flat_data_2 )) (PreH24 : (LengthsPrefix items_2 line lengths_data_2 )) (PreH25 : ((Zlength (cells_2)) = 1005)) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells_2 __default__App_option_Z) = (Some ((Znth k_2 active_2 0)))))) (PreH27 : ((Znth (depth - 1 ) cells_2 __default__App_option_Z) = (Some ((Znth (depth - 1 ) active_2 0))))),
  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active_2 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells_2 )
  **  (IntArray.seg flat_pre 0 total flat_data_2 )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data_2 )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  EX (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (active: (@list Z)) (target: (@list Z)) (items: (@list (@list Z))),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 < line) ”
  &&  “ (line < n_pre) ”
  &&  “ (x = (Znth (line) (last_numbers) (0))) ”
  &&  “ (x <> 1) ”
  &&  “ (target = (Znth (line) (items) ((@nil Z)))) ”
  &&  “ (1 <= (depth - 1 )) ”
  &&  “ ((depth - 1 ) <= line) ”
  &&  “ ((depth - 1 ) = (Zlength (active))) ”
  &&  “ (PopTarget active target x ) ”
  &&  “ (BoundedItem n_pre active ) ”
  &&  “ (total = (Zlength (flat_data))) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= (line * n_pre )) ”
  &&  “ (FlatPrefix items line flat_data ) ”
  &&  “ (LengthsPrefix items line lengths_data ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (depth - 1 ))) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  “ ((Znth ((depth - 1 ) - 1 ) cells __default__App_option_Z) = (Some ((Znth ((depth - 1 ) - 1 ) active 0)))) ”
  &&  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + (((depth - 1 ) - 1 ) * sizeof(INT)))) # Int  |-> (Znth ((depth - 1 ) - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) ((depth - 1 ) - 1 ) 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
) \/
(
forall (last_numbers: (@list Z)) (n_pre: Z) (cells_2: (@list (@option Z))) (lengths_data_2: (@list Z)) (flat_data_2: (@list Z)) (total: Z) (active_2: (@list Z)) (depth: Z) (target_2: (@list Z)) (x: Z) (line: Z) (items_2: (@list (@list Z))) __default__App_option_Z (PreH1 : ((Znth (depth - 1 ) active_2 0) <= INT_MAX)) (PreH2 : ((Znth (depth - 1 ) active_2 0) >= INT_MIN)) (PreH3 : (((Znth (depth - 1 ) active_2 0) + 1 ) <> x)) (PreH4 : (depth <> 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (n_pre = (Zlength (last_numbers)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH9 : (Pre last_numbers )) (PreH10 : (Spec last_numbers items_2 )) (PreH11 : ((Zlength (items_2)) = n_pre)) (PreH12 : (0 < line)) (PreH13 : (line < n_pre)) (PreH14 : (x = (Znth (line) (last_numbers) (0)))) (PreH15 : (x <> 1)) (PreH16 : (target_2 = (Znth (line) (items_2) ((@nil Z))))) (PreH17 : (1 <= depth)) (PreH18 : (depth <= line)) (PreH19 : (depth = (Zlength (active_2)))) (PreH20 : (PopTarget active_2 target_2 x )) (PreH21 : (BoundedItem n_pre active_2 )) (PreH22 : (total = (Zlength (flat_data_2)))) (PreH23 : (0 <= total)) (PreH24 : (total <= (line * n_pre ))) (PreH25 : (FlatPrefix items_2 line flat_data_2 )) (PreH26 : (LengthsPrefix items_2 line lengths_data_2 )) (PreH27 : ((Zlength (cells_2)) = 1005)) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells_2 __default__App_option_Z) = (Some ((Znth k_2 active_2 0)))))) (PreH29 : ((Znth (depth - 1 ) cells_2 __default__App_option_Z) = (Some ((Znth (depth - 1 ) active_2 0))))),
  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> (Znth (depth - 1 ) active_2 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells_2 )
|--
  EX (cells: (@list (@option Z))) (active: (@list Z)) (items: (@list (@list Z))),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 < line) ”
  &&  “ (line < n_pre) ”
  &&  “ (x = (Znth (line) (last_numbers) (0))) ”
  &&  “ (x <> 1) ”
  &&  “ (1 <= (depth - 1 )) ”
  &&  “ ((depth - 1 ) <= line) ”
  &&  “ ((depth - 1 ) = (Zlength (active))) ”
  &&  “ (PopTarget active (Znth (line) (items) ((@nil Z))) x ) ”
  &&  “ (BoundedItem n_pre active ) ”
  &&  “ (total = (Zlength (flat_data_2))) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= (line * n_pre )) ”
  &&  “ (FlatPrefix items line flat_data_2 ) ”
  &&  “ (LengthsPrefix items line lengths_data_2 ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (depth - 1 ))) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  “ ((Znth ((depth - 1 ) - 1 ) cells __default__App_option_Z) = (Some ((Znth ((depth - 1 ) - 1 ) active 0)))) ”
  &&  (((( &( "stack" ) ) + (((depth - 1 ) - 1 ) * sizeof(INT)))) # Int  |-> (Znth ((depth - 1 ) - 1 ) active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) ((depth - 1 ) - 1 ) 0 1005 cells )
).

Definition solver_entail_wit_5_1 :=
(
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells_2: (@list (@option Z))) (lengths_data_2: (@list Z)) (flat_data_2: (@list Z)) (total: Z) (active_2: (@list Z)) (depth: Z) (line: Z) (items_2: (@list (@list Z))) __default__App_option_Z (PreH1 : ((Znth line last_numbers 0) = 1)) (PreH2 : (line < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) (0))) /\ ((Znth (k_3) (last_numbers) (0)) <= n_pre)))) (PreH7 : (Pre last_numbers )) (PreH8 : (Spec last_numbers items_2 )) (PreH9 : ((Zlength (items_2)) = n_pre)) (PreH10 : (0 <= line)) (PreH11 : (line <= n_pre)) (PreH12 : (0 <= depth)) (PreH13 : (depth <= line)) (PreH14 : (depth = (Zlength (active_2)))) (PreH15 : (CurrentItem items_2 line active_2 )) (PreH16 : (BoundedItem n_pre active_2 )) (PreH17 : (total = (Zlength (flat_data_2)))) (PreH18 : (0 <= total)) (PreH19 : (total <= (line * n_pre ))) (PreH20 : (FlatPrefix items_2 line flat_data_2 )) (PreH21 : (LengthsPrefix items_2 line lengths_data_2 )) (PreH22 : ((Zlength (cells_2)) = 1005)) (PreH23 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 0)))))),
  (IntArray.mixed_full ( &( "stack" ) ) 1005 (replace_Znth (depth) ((Some (1))) (cells_2)) )
  **  (IntArray.full values_pre n_pre last_numbers )
  **  ((( &( "x" ) )) # Int  |-> (Znth line last_numbers 0))
  **  (IntArray.seg flat_pre 0 total flat_data_2 )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data_2 )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  EX (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (active: (@list Z)) (items: (@list (@list Z))),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 <= line) ”
  &&  “ (line < n_pre) ”
  &&  “ (active = (Znth (line) (items) ((@nil Z)))) ”
  &&  “ (1 <= (depth + 1 )) ”
  &&  “ ((depth + 1 ) <= (line + 1 )) ”
  &&  “ ((depth + 1 ) = (Zlength (active))) ”
  &&  “ (BoundedItem n_pre active ) ”
  &&  “ (total = (Zlength (flat_data))) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= (line * n_pre )) ”
  &&  “ (FlatPrefix items line flat_data ) ”
  &&  “ (LengthsPrefix items line lengths_data ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (depth + 1 ))) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  ((( &( "x" ) )) # Int  |->_)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
) \/
(
forall (last_numbers: (@list Z)) (n_pre: Z) (cells_2: (@list (@option Z))) (lengths_data_2: (@list Z)) (flat_data_2: (@list Z)) (total: Z) (active_2: (@list Z)) (depth: Z) (line: Z) (items_2: (@list (@list Z))) __default__App_option_Z (PreH1 : ((Znth line last_numbers 0) = 1)) (PreH2 : (line < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) (0))) /\ ((Znth (k_3) (last_numbers) (0)) <= n_pre)))) (PreH7 : (Pre last_numbers )) (PreH8 : (Spec last_numbers items_2 )) (PreH9 : ((Zlength (items_2)) = n_pre)) (PreH10 : (0 <= line)) (PreH11 : (line <= n_pre)) (PreH12 : (0 <= depth)) (PreH13 : (depth <= line)) (PreH14 : (depth = (Zlength (active_2)))) (PreH15 : (CurrentItem items_2 line active_2 )) (PreH16 : (BoundedItem n_pre active_2 )) (PreH17 : (total = (Zlength (flat_data_2)))) (PreH18 : (0 <= total)) (PreH19 : (total <= (line * n_pre ))) (PreH20 : (FlatPrefix items_2 line flat_data_2 )) (PreH21 : (LengthsPrefix items_2 line lengths_data_2 )) (PreH22 : ((Zlength (cells_2)) = 1005)) (PreH23 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 0)))))),
  TT && emp 
|--
  EX (items: (@list (@list Z))),
  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = (Zlength (last_numbers))) ”
  &&  “ (1 <= ((Zlength (active_2)) + 1 )) ”
  &&  “ (((Zlength (active_2)) + 1 ) <= (line + 1 )) ”
  &&  “ (((Zlength (active_2)) + 1 ) = (Zlength ((Znth (line) (items) ((@nil Z)))))) ”
  &&  “ (BoundedItem (Zlength (last_numbers)) (Znth (line) (items) ((@nil Z))) ) ”
  &&  “ (FlatPrefix items line flat_data_2 ) ”
  &&  “ (LengthsPrefix items line lengths_data_2 ) ”
  &&  “ ((Zlength ((replace_Znth ((Zlength (active_2))) ((Some (1))) (cells_2)))) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < ((Zlength (active_2)) + 1 ))) -> ((Znth k_2 (replace_Znth ((Zlength (active_2))) ((Some (1))) (cells_2)) __default__App_option_Z) = (Some ((Znth k_2 (Znth (line) (items) ((@nil Z))) 0))))) ”
  &&  emp
).

Definition solver_entail_wit_5_2 :=
(
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells_2: (@list (@option Z))) (lengths_data_2: (@list Z)) (flat_data_2: (@list Z)) (total: Z) (active_2: (@list Z)) (depth: Z) (target: (@list Z)) (x: Z) (line: Z) (items_2: (@list (@list Z))) __default__App_option_Z (PreH1 : (((Znth (depth - 1 ) active_2 0) + 1 ) = x)) (PreH2 : (depth <> 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) (0))) /\ ((Znth (k_3) (last_numbers) (0)) <= n_pre)))) (PreH7 : (Pre last_numbers )) (PreH8 : (Spec last_numbers items_2 )) (PreH9 : ((Zlength (items_2)) = n_pre)) (PreH10 : (0 < line)) (PreH11 : (line < n_pre)) (PreH12 : (x = (Znth (line) (last_numbers) (0)))) (PreH13 : (x <> 1)) (PreH14 : (target = (Znth (line) (items_2) ((@nil Z))))) (PreH15 : (1 <= depth)) (PreH16 : (depth <= line)) (PreH17 : (depth = (Zlength (active_2)))) (PreH18 : (PopTarget active_2 target x )) (PreH19 : (BoundedItem n_pre active_2 )) (PreH20 : (total = (Zlength (flat_data_2)))) (PreH21 : (0 <= total)) (PreH22 : (total <= (line * n_pre ))) (PreH23 : (FlatPrefix items_2 line flat_data_2 )) (PreH24 : (LengthsPrefix items_2 line lengths_data_2 )) (PreH25 : ((Zlength (cells_2)) = 1005)) (PreH26 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 0)))))) (PreH27 : ((Znth (depth - 1 ) cells_2 __default__App_option_Z) = (Some ((Znth (depth - 1 ) active_2 0))))),
  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> x)
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells_2 )
  **  (IntArray.seg flat_pre 0 total flat_data_2 )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data_2 )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  EX (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (active: (@list Z)) (items: (@list (@list Z))),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 <= line) ”
  &&  “ (line < n_pre) ”
  &&  “ (active = (Znth (line) (items) ((@nil Z)))) ”
  &&  “ (1 <= depth) ”
  &&  “ (depth <= (line + 1 )) ”
  &&  “ (depth = (Zlength (active))) ”
  &&  “ (BoundedItem n_pre active ) ”
  &&  “ (total = (Zlength (flat_data))) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= (line * n_pre )) ”
  &&  “ (FlatPrefix items line flat_data ) ”
  &&  “ (LengthsPrefix items line lengths_data ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  ((( &( "x" ) )) # Int  |->_)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
) \/
(
forall (last_numbers: (@list Z)) (n_pre: Z) (cells_2: (@list (@option Z))) (lengths_data_2: (@list Z)) (flat_data_2: (@list Z)) (total: Z) (active_2: (@list Z)) (depth: Z) (target: (@list Z)) (x: Z) (line: Z) (items_2: (@list (@list Z))) __default__App_option_Z (PreH1 : (x <= INT_MAX)) (PreH2 : (x >= INT_MIN)) (PreH3 : (((Znth (depth - 1 ) active_2 0) + 1 ) = x)) (PreH4 : (depth <> 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (n_pre = (Zlength (last_numbers)))) (PreH8 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) (0))) /\ ((Znth (k_3) (last_numbers) (0)) <= n_pre)))) (PreH9 : (Pre last_numbers )) (PreH10 : (Spec last_numbers items_2 )) (PreH11 : ((Zlength (items_2)) = n_pre)) (PreH12 : (0 < line)) (PreH13 : (line < n_pre)) (PreH14 : (x = (Znth (line) (last_numbers) (0)))) (PreH15 : (x <> 1)) (PreH16 : (target = (Znth (line) (items_2) ((@nil Z))))) (PreH17 : (1 <= depth)) (PreH18 : (depth <= line)) (PreH19 : (depth = (Zlength (active_2)))) (PreH20 : (PopTarget active_2 target x )) (PreH21 : (BoundedItem n_pre active_2 )) (PreH22 : (total = (Zlength (flat_data_2)))) (PreH23 : (0 <= total)) (PreH24 : (total <= (line * n_pre ))) (PreH25 : (FlatPrefix items_2 line flat_data_2 )) (PreH26 : (LengthsPrefix items_2 line lengths_data_2 )) (PreH27 : ((Zlength (cells_2)) = 1005)) (PreH28 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 0)))))) (PreH29 : ((Znth (depth - 1 ) cells_2 __default__App_option_Z) = (Some ((Znth (depth - 1 ) active_2 0))))),
  (((( &( "stack" ) ) + ((depth - 1 ) * sizeof(INT)))) # Int  |-> x)
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) (depth - 1 ) 0 1005 cells_2 )
|--
  EX (cells: (@list (@option Z))) (items: (@list (@list Z))),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 <= line) ”
  &&  “ (line < n_pre) ”
  &&  “ (1 <= depth) ”
  &&  “ (depth <= (line + 1 )) ”
  &&  “ (depth = (Zlength ((Znth (line) (items) ((@nil Z)))))) ”
  &&  “ (BoundedItem n_pre (Znth (line) (items) ((@nil Z))) ) ”
  &&  “ (total = (Zlength (flat_data_2))) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= (line * n_pre )) ”
  &&  “ (FlatPrefix items line flat_data_2 ) ”
  &&  “ (LengthsPrefix items line lengths_data_2 ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 (Znth (line) (items) ((@nil Z))) 0))))) ”
  &&  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
).

Definition solver_entail_wit_6 :=
(
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (items_2: (@list (@list Z))) (cells_2: (@list (@option Z))) (active_2: (@list Z)) (flat_data_2: (@list Z)) (lengths_data_2: (@list Z)) (line: Z) (depth: Z) (total: Z) __default__App_option_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) (0))) /\ ((Znth (k_3) (last_numbers) (0)) <= n_pre)))) (PreH5 : (Pre last_numbers )) (PreH6 : (Spec last_numbers items_2 )) (PreH7 : ((Zlength (items_2)) = n_pre)) (PreH8 : (0 <= line)) (PreH9 : (line < n_pre)) (PreH10 : (active_2 = (Znth (line) (items_2) ((@nil Z))))) (PreH11 : (1 <= depth)) (PreH12 : (depth <= (line + 1 ))) (PreH13 : (depth = (Zlength (active_2)))) (PreH14 : (BoundedItem n_pre active_2 )) (PreH15 : (total = (Zlength (flat_data_2)))) (PreH16 : (0 <= total)) (PreH17 : (total <= (line * n_pre ))) (PreH18 : (FlatPrefix items_2 line flat_data_2 )) (PreH19 : (LengthsPrefix items_2 line lengths_data_2 )) (PreH20 : ((Zlength (cells_2)) = 1005)) (PreH21 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 0)))))),
  (IntArray.seg lengths_pre 0 (line + 1 ) (app (lengths_data_2) ((cons (depth) ((@nil Z))))) )
  **  (IntArray.undef_seg lengths_pre (line + 1 ) n_pre )
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells_2 )
  **  (IntArray.seg flat_pre 0 total flat_data_2 )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
|--
  EX (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (flat_before: (@list Z)) (active: (@list Z)) (items: (@list (@list Z))),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 <= line) ”
  &&  “ (line < n_pre) ”
  &&  “ (active = (Znth (line) (items) ((@nil Z)))) ”
  &&  “ (1 <= depth) ”
  &&  “ (depth <= (line + 1 )) ”
  &&  “ ((line + 1 ) <= n_pre) ”
  &&  “ (depth = (Zlength (active))) ”
  &&  “ (BoundedItem n_pre active ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= depth) ”
  &&  “ (FlatPrefix items line flat_before ) ”
  &&  “ (flat_data = (app (flat_before) ((sublist (0) (0) (active))))) ”
  &&  “ (total = (Zlength (flat_data))) ”
  &&  “ (0 <= total) ”
  &&  “ ((total + (depth - 0 ) ) <= ((line + 1 ) * n_pre )) ”
  &&  “ (((line + 1 ) * n_pre ) <= (n_pre * n_pre )) ”
  &&  “ (LengthsPrefix items (line + 1 ) lengths_data ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 (line + 1 ) lengths_data )
  **  (IntArray.undef_seg lengths_pre (line + 1 ) n_pre )
) \/
(
forall (last_numbers: (@list Z)) (n_pre: Z) (items_2: (@list (@list Z))) (cells_2: (@list (@option Z))) (active_2: (@list Z)) (flat_data_2: (@list Z)) (lengths_data_2: (@list Z)) (line: Z) (depth: Z) (total: Z) __default__App_option_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) (0))) /\ ((Znth (k_3) (last_numbers) (0)) <= n_pre)))) (PreH5 : (Pre last_numbers )) (PreH6 : (Spec last_numbers items_2 )) (PreH7 : ((Zlength (items_2)) = n_pre)) (PreH8 : (0 <= line)) (PreH9 : (line < n_pre)) (PreH10 : (active_2 = (Znth (line) (items_2) ((@nil Z))))) (PreH11 : (1 <= depth)) (PreH12 : (depth <= (line + 1 ))) (PreH13 : (depth = (Zlength (active_2)))) (PreH14 : (BoundedItem n_pre active_2 )) (PreH15 : (total = (Zlength (flat_data_2)))) (PreH16 : (0 <= total)) (PreH17 : (total <= (line * n_pre ))) (PreH18 : (FlatPrefix items_2 line flat_data_2 )) (PreH19 : (LengthsPrefix items_2 line lengths_data_2 )) (PreH20 : ((Zlength (cells_2)) = 1005)) (PreH21 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 0)))))),
  TT && emp 
|--
  EX (flat_before: (@list Z)) (items: (@list (@list Z))),
  “ (flat_data_2 = (app (flat_before) ((sublist (0) (0) ((Znth (line) (items) ((@nil Z)))))))) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = (Zlength (last_numbers))) ”
  &&  “ ((line + 1 ) <= (Zlength (last_numbers))) ”
  &&  “ ((Zlength (active_2)) = (Zlength ((Znth (line) (items) ((@nil Z)))))) ”
  &&  “ (BoundedItem (Zlength (last_numbers)) (Znth (line) (items) ((@nil Z))) ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (Zlength (active_2))) ”
  &&  “ (FlatPrefix items line flat_before ) ”
  &&  “ ((Zlength (flat_data_2)) = (Zlength ((app (flat_before) ((sublist (0) (0) ((Znth (line) (items) ((@nil Z)))))))))) ”
  &&  “ (((Zlength (flat_data_2)) + ((Zlength (active_2)) - 0 ) ) <= ((line + 1 ) * (Zlength (last_numbers)) )) ”
  &&  “ (((line + 1 ) * (Zlength (last_numbers)) ) <= ((Zlength (last_numbers)) * (Zlength (last_numbers)) )) ”
  &&  “ (LengthsPrefix items (line + 1 ) (app (lengths_data_2) ((cons ((Zlength (active_2))) ((@nil Z))))) ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (active_2)))) -> ((Znth k_2 cells_2 __default__App_option_Z) = (Some ((Znth k_2 (Znth (line) (items) ((@nil Z))) 0))))) ”
  &&  emp
).

Definition solver_entail_wit_7 :=
(
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells_2: (@list (@option Z))) (lengths_data_2: (@list Z)) (total: Z) (flat_data_2: (@list Z)) (flat_before_2: (@list Z)) (i: Z) (depth: Z) (active_2: (@list Z)) (line: Z) (items_2: (@list (@list Z))) __default__App_option_Z (PreH1 : (i < depth)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) (0))) /\ ((Znth (k_3) (last_numbers) (0)) <= n_pre)))) (PreH6 : (Pre last_numbers )) (PreH7 : (Spec last_numbers items_2 )) (PreH8 : ((Zlength (items_2)) = n_pre)) (PreH9 : (0 <= line)) (PreH10 : (line < n_pre)) (PreH11 : (active_2 = (Znth (line) (items_2) ((@nil Z))))) (PreH12 : (1 <= depth)) (PreH13 : (depth <= (line + 1 ))) (PreH14 : ((line + 1 ) <= n_pre)) (PreH15 : (depth = (Zlength (active_2)))) (PreH16 : (BoundedItem n_pre active_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= depth)) (PreH19 : (FlatPrefix items_2 line flat_before_2 )) (PreH20 : (flat_data_2 = (app (flat_before_2) ((sublist (0) (i) (active_2)))))) (PreH21 : (total = (Zlength (flat_data_2)))) (PreH22 : (0 <= total)) (PreH23 : ((total + (depth - i ) ) <= ((line + 1 ) * n_pre ))) (PreH24 : (((line + 1 ) * n_pre ) <= (n_pre * n_pre ))) (PreH25 : (LengthsPrefix items_2 (line + 1 ) lengths_data_2 )) (PreH26 : ((Zlength (cells_2)) = 1005)) (PreH27 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 0)))))),
  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells_2 )
  **  (IntArray.seg flat_pre 0 total flat_data_2 )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 (line + 1 ) lengths_data_2 )
  **  (IntArray.undef_seg lengths_pre (line + 1 ) n_pre )
|--
  EX (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (flat_before: (@list Z)) (active: (@list Z)) (items: (@list (@list Z))),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 <= line) ”
  &&  “ (line < n_pre) ”
  &&  “ (active = (Znth (line) (items) ((@nil Z)))) ”
  &&  “ (1 <= depth) ”
  &&  “ (depth <= (line + 1 )) ”
  &&  “ ((line + 1 ) <= n_pre) ”
  &&  “ (depth = (Zlength (active))) ”
  &&  “ (BoundedItem n_pre active ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < depth) ”
  &&  “ (FlatPrefix items line flat_before ) ”
  &&  “ (flat_data = (app (flat_before) ((sublist (0) (i) (active))))) ”
  &&  “ (total = (Zlength (flat_data))) ”
  &&  “ (0 <= total) ”
  &&  “ ((total + (depth - i ) ) <= ((line + 1 ) * n_pre )) ”
  &&  “ (((line + 1 ) * n_pre ) <= (n_pre * n_pre )) ”
  &&  “ (LengthsPrefix items (line + 1 ) lengths_data ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  “ ((Znth i cells __default__App_option_Z) = (Some ((Znth i active 0)))) ”
  &&  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth i active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) i 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 (line + 1 ) lengths_data )
  **  (IntArray.undef_seg lengths_pre (line + 1 ) n_pre )
) \/
(
forall (last_numbers: (@list Z)) (n_pre: Z) (cells_2: (@list (@option Z))) (lengths_data_2: (@list Z)) (total: Z) (flat_data_2: (@list Z)) (flat_before_2: (@list Z)) (i: Z) (depth: Z) (active_2: (@list Z)) (line: Z) (items_2: (@list (@list Z))) __default__App_option_Z (PreH1 : (i < depth)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) (0))) /\ ((Znth (k_3) (last_numbers) (0)) <= n_pre)))) (PreH6 : (Pre last_numbers )) (PreH7 : (Spec last_numbers items_2 )) (PreH8 : ((Zlength (items_2)) = n_pre)) (PreH9 : (0 <= line)) (PreH10 : (line < n_pre)) (PreH11 : (active_2 = (Znth (line) (items_2) ((@nil Z))))) (PreH12 : (1 <= depth)) (PreH13 : (depth <= (line + 1 ))) (PreH14 : ((line + 1 ) <= n_pre)) (PreH15 : (depth = (Zlength (active_2)))) (PreH16 : (BoundedItem n_pre active_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= depth)) (PreH19 : (FlatPrefix items_2 line flat_before_2 )) (PreH20 : (flat_data_2 = (app (flat_before_2) ((sublist (0) (i) (active_2)))))) (PreH21 : (total = (Zlength (flat_data_2)))) (PreH22 : (0 <= total)) (PreH23 : ((total + (depth - i ) ) <= ((line + 1 ) * n_pre ))) (PreH24 : (((line + 1 ) * n_pre ) <= (n_pre * n_pre ))) (PreH25 : (LengthsPrefix items_2 (line + 1 ) lengths_data_2 )) (PreH26 : ((Zlength (cells_2)) = 1005)) (PreH27 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 0)))))),
  TT && emp 
|--
  EX (flat_before: (@list Z)) (items: (@list (@list Z))),
  “ ((Znth i cells_2 __default__App_option_Z) = (Some ((Znth i (Znth (line) (items) ((@nil Z))) 0)))) ”
  &&  “ ((app (flat_before_2) ((sublist (0) (i) (active_2)))) = (app (flat_before) ((sublist (0) (i) ((Znth (line) (items) ((@nil Z)))))))) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = (Zlength (last_numbers))) ”
  &&  “ ((Zlength (active_2)) = (Zlength ((Znth (line) (items) ((@nil Z)))))) ”
  &&  “ (BoundedItem (Zlength (last_numbers)) (Znth (line) (items) ((@nil Z))) ) ”
  &&  “ (FlatPrefix items line flat_before ) ”
  &&  “ ((Zlength (flat_data_2)) = (Zlength ((app (flat_before) ((sublist (0) (i) ((Znth (line) (items) ((@nil Z)))))))))) ”
  &&  “ (LengthsPrefix items (line + 1 ) lengths_data_2 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (active_2)))) -> ((Znth k_2 cells_2 __default__App_option_Z) = (Some ((Znth k_2 (Znth (line) (items) ((@nil Z))) 0))))) ”
  &&  “ ((Znth i cells_2 __default__App_option_Z) = (Some ((Znth i (Znth (line) (items) ((@nil Z))) 0)))) ”
  &&  emp
).

Definition solver_entail_wit_8 :=
(
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (items_2: (@list (@list Z))) (cells_2: (@list (@option Z))) (active_2: (@list Z)) (flat_before_2: (@list Z)) (flat_data_2: (@list Z)) (lengths_data_2: (@list Z)) (line: Z) (depth: Z) (i: Z) (total: Z) __default__App_option_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) (0))) /\ ((Znth (k_3) (last_numbers) (0)) <= n_pre)))) (PreH5 : (Pre last_numbers )) (PreH6 : (Spec last_numbers items_2 )) (PreH7 : ((Zlength (items_2)) = n_pre)) (PreH8 : (0 <= line)) (PreH9 : (line < n_pre)) (PreH10 : (active_2 = (Znth (line) (items_2) ((@nil Z))))) (PreH11 : (1 <= depth)) (PreH12 : (depth <= (line + 1 ))) (PreH13 : ((line + 1 ) <= n_pre)) (PreH14 : (depth = (Zlength (active_2)))) (PreH15 : (BoundedItem n_pre active_2 )) (PreH16 : (0 <= i)) (PreH17 : (i < depth)) (PreH18 : (FlatPrefix items_2 line flat_before_2 )) (PreH19 : (flat_data_2 = (app (flat_before_2) ((sublist (0) (i) (active_2)))))) (PreH20 : (total = (Zlength (flat_data_2)))) (PreH21 : (0 <= total)) (PreH22 : ((total + (depth - i ) ) <= ((line + 1 ) * n_pre ))) (PreH23 : (((line + 1 ) * n_pre ) <= (n_pre * n_pre ))) (PreH24 : (LengthsPrefix items_2 (line + 1 ) lengths_data_2 )) (PreH25 : ((Zlength (cells_2)) = 1005)) (PreH26 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 0)))))) (PreH27 : ((Znth i cells_2 __default__App_option_Z) = (Some ((Znth i active_2 0))))),
  (IntArray.seg flat_pre 0 (total + 1 ) (app (flat_data_2) ((cons ((Znth i active_2 0)) ((@nil Z))))) )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells_2 )
  **  (IntArray.undef_seg flat_pre (total + 1 ) (n_pre * n_pre ) )
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.seg lengths_pre 0 (line + 1 ) lengths_data_2 )
  **  (IntArray.undef_seg lengths_pre (line + 1 ) n_pre )
|--
  EX (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (flat_before: (@list Z)) (active: (@list Z)) (items: (@list (@list Z))),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 <= line) ”
  &&  “ (line < n_pre) ”
  &&  “ (active = (Znth (line) (items) ((@nil Z)))) ”
  &&  “ (1 <= depth) ”
  &&  “ (depth <= (line + 1 )) ”
  &&  “ ((line + 1 ) <= n_pre) ”
  &&  “ (depth = (Zlength (active))) ”
  &&  “ (BoundedItem n_pre active ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= depth) ”
  &&  “ (FlatPrefix items line flat_before ) ”
  &&  “ (flat_data = (app (flat_before) ((sublist (0) ((i + 1 )) (active))))) ”
  &&  “ ((total + 1 ) = (Zlength (flat_data))) ”
  &&  “ (0 <= (total + 1 )) ”
  &&  “ (((total + 1 ) + (depth - (i + 1 ) ) ) <= ((line + 1 ) * n_pre )) ”
  &&  “ (((line + 1 ) * n_pre ) <= (n_pre * n_pre )) ”
  &&  “ (LengthsPrefix items (line + 1 ) lengths_data ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
  **  (IntArray.seg flat_pre 0 (total + 1 ) flat_data )
  **  (IntArray.undef_seg flat_pre (total + 1 ) (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 (line + 1 ) lengths_data )
  **  (IntArray.undef_seg lengths_pre (line + 1 ) n_pre )
) \/
(
forall (last_numbers: (@list Z)) (n_pre: Z) (items_2: (@list (@list Z))) (cells_2: (@list (@option Z))) (active_2: (@list Z)) (flat_before_2: (@list Z)) (flat_data_2: (@list Z)) (lengths_data_2: (@list Z)) (line: Z) (depth: Z) (i: Z) (total: Z) __default__App_option_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) (0))) /\ ((Znth (k_3) (last_numbers) (0)) <= n_pre)))) (PreH5 : (Pre last_numbers )) (PreH6 : (Spec last_numbers items_2 )) (PreH7 : ((Zlength (items_2)) = n_pre)) (PreH8 : (0 <= line)) (PreH9 : (line < n_pre)) (PreH10 : (active_2 = (Znth (line) (items_2) ((@nil Z))))) (PreH11 : (1 <= depth)) (PreH12 : (depth <= (line + 1 ))) (PreH13 : ((line + 1 ) <= n_pre)) (PreH14 : (depth = (Zlength (active_2)))) (PreH15 : (BoundedItem n_pre active_2 )) (PreH16 : (0 <= i)) (PreH17 : (i < depth)) (PreH18 : (FlatPrefix items_2 line flat_before_2 )) (PreH19 : (flat_data_2 = (app (flat_before_2) ((sublist (0) (i) (active_2)))))) (PreH20 : (total = (Zlength (flat_data_2)))) (PreH21 : (0 <= total)) (PreH22 : ((total + (depth - i ) ) <= ((line + 1 ) * n_pre ))) (PreH23 : (((line + 1 ) * n_pre ) <= (n_pre * n_pre ))) (PreH24 : (LengthsPrefix items_2 (line + 1 ) lengths_data_2 )) (PreH25 : ((Zlength (cells_2)) = 1005)) (PreH26 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 0)))))) (PreH27 : ((Znth i cells_2 __default__App_option_Z) = (Some ((Znth i active_2 0))))),
  TT && emp 
|--
  EX (flat_before: (@list Z)) (items: (@list (@list Z))),
  “ ((app ((app (flat_before_2) ((sublist (0) (i) (active_2))))) ((cons ((Znth i (Znth (line) (items_2) ((@nil Z))) 0)) ((@nil Z))))) = (app (flat_before) ((sublist (0) ((i + 1 )) ((Znth (line) (items) ((@nil Z)))))))) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = (Zlength (last_numbers))) ”
  &&  “ ((Zlength (active_2)) = (Zlength ((Znth (line) (items) ((@nil Z)))))) ”
  &&  “ (BoundedItem (Zlength (last_numbers)) (Znth (line) (items) ((@nil Z))) ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (active_2))) ”
  &&  “ (FlatPrefix items line flat_before ) ”
  &&  “ (((Zlength (flat_data_2)) + 1 ) = (Zlength ((app (flat_before) ((sublist (0) ((i + 1 )) ((Znth (line) (items) ((@nil Z)))))))))) ”
  &&  “ (0 <= ((Zlength (flat_data_2)) + 1 )) ”
  &&  “ ((((Zlength (flat_data_2)) + 1 ) + ((Zlength (active_2)) - (i + 1 ) ) ) <= ((line + 1 ) * (Zlength (last_numbers)) )) ”
  &&  “ (LengthsPrefix items (line + 1 ) lengths_data_2 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (active_2)))) -> ((Znth k_2 cells_2 __default__App_option_Z) = (Some ((Znth k_2 (Znth (line) (items) ((@nil Z))) 0))))) ”
  &&  emp
).

Definition solver_entail_wit_9 :=
(
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells_2: (@list (@option Z))) (lengths_data_2: (@list Z)) (total: Z) (flat_data_2: (@list Z)) (flat_before: (@list Z)) (i: Z) (depth: Z) (active_2: (@list Z)) (line: Z) (items_2: (@list (@list Z))) __default__App_option_Z (PreH1 : (i >= depth)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) (0))) /\ ((Znth (k_3) (last_numbers) (0)) <= n_pre)))) (PreH6 : (Pre last_numbers )) (PreH7 : (Spec last_numbers items_2 )) (PreH8 : ((Zlength (items_2)) = n_pre)) (PreH9 : (0 <= line)) (PreH10 : (line < n_pre)) (PreH11 : (active_2 = (Znth (line) (items_2) ((@nil Z))))) (PreH12 : (1 <= depth)) (PreH13 : (depth <= (line + 1 ))) (PreH14 : ((line + 1 ) <= n_pre)) (PreH15 : (depth = (Zlength (active_2)))) (PreH16 : (BoundedItem n_pre active_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= depth)) (PreH19 : (FlatPrefix items_2 line flat_before )) (PreH20 : (flat_data_2 = (app (flat_before) ((sublist (0) (i) (active_2)))))) (PreH21 : (total = (Zlength (flat_data_2)))) (PreH22 : (0 <= total)) (PreH23 : ((total + (depth - i ) ) <= ((line + 1 ) * n_pre ))) (PreH24 : (((line + 1 ) * n_pre ) <= (n_pre * n_pre ))) (PreH25 : (LengthsPrefix items_2 (line + 1 ) lengths_data_2 )) (PreH26 : ((Zlength (cells_2)) = 1005)) (PreH27 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 0)))))),
  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells_2 )
  **  (IntArray.seg flat_pre 0 total flat_data_2 )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 (line + 1 ) lengths_data_2 )
  **  (IntArray.undef_seg lengths_pre (line + 1 ) n_pre )
|--
  EX (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (active: (@list Z)) (items: (@list (@list Z))),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 <= (line + 1 )) ”
  &&  “ ((line + 1 ) <= n_pre) ”
  &&  “ (0 <= depth) ”
  &&  “ (depth <= (line + 1 )) ”
  &&  “ (depth = (Zlength (active))) ”
  &&  “ (CurrentItem items (line + 1 ) active ) ”
  &&  “ (BoundedItem n_pre active ) ”
  &&  “ (total = (Zlength (flat_data))) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= ((line + 1 ) * n_pre )) ”
  &&  “ (FlatPrefix items (line + 1 ) flat_data ) ”
  &&  “ (LengthsPrefix items (line + 1 ) lengths_data ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 (line + 1 ) lengths_data )
  **  (IntArray.undef_seg lengths_pre (line + 1 ) n_pre )
) \/
(
forall (last_numbers: (@list Z)) (n_pre: Z) (cells_2: (@list (@option Z))) (lengths_data_2: (@list Z)) (total: Z) (flat_data_2: (@list Z)) (flat_before: (@list Z)) (i: Z) (depth: Z) (active_2: (@list Z)) (line: Z) (items_2: (@list (@list Z))) __default__App_option_Z (PreH1 : (i >= depth)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) (0))) /\ ((Znth (k_3) (last_numbers) (0)) <= n_pre)))) (PreH6 : (Pre last_numbers )) (PreH7 : (Spec last_numbers items_2 )) (PreH8 : ((Zlength (items_2)) = n_pre)) (PreH9 : (0 <= line)) (PreH10 : (line < n_pre)) (PreH11 : (active_2 = (Znth (line) (items_2) ((@nil Z))))) (PreH12 : (1 <= depth)) (PreH13 : (depth <= (line + 1 ))) (PreH14 : ((line + 1 ) <= n_pre)) (PreH15 : (depth = (Zlength (active_2)))) (PreH16 : (BoundedItem n_pre active_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= depth)) (PreH19 : (FlatPrefix items_2 line flat_before )) (PreH20 : (flat_data_2 = (app (flat_before) ((sublist (0) (i) (active_2)))))) (PreH21 : (total = (Zlength (flat_data_2)))) (PreH22 : (0 <= total)) (PreH23 : ((total + (depth - i ) ) <= ((line + 1 ) * n_pre ))) (PreH24 : (((line + 1 ) * n_pre ) <= (n_pre * n_pre ))) (PreH25 : (LengthsPrefix items_2 (line + 1 ) lengths_data_2 )) (PreH26 : ((Zlength (cells_2)) = 1005)) (PreH27 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 0)))))),
  TT && emp 
|--
  EX (active: (@list Z)) (items: (@list (@list Z))),
  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = (Zlength (last_numbers))) ”
  &&  “ (0 <= (line + 1 )) ”
  &&  “ (0 <= (Zlength (active_2))) ”
  &&  “ ((Zlength (active_2)) = (Zlength (active))) ”
  &&  “ (CurrentItem items (line + 1 ) active ) ”
  &&  “ (BoundedItem (Zlength (last_numbers)) active ) ”
  &&  “ ((Zlength (flat_data_2)) <= ((line + 1 ) * (Zlength (last_numbers)) )) ”
  &&  “ (FlatPrefix items (line + 1 ) (app (flat_before) ((sublist (0) (i) (active_2)))) ) ”
  &&  “ (LengthsPrefix items (line + 1 ) lengths_data_2 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (active_2)))) -> ((Znth k_2 cells_2 __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  emp
).

Definition solver_entail_wit_10 :=
(
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data_2: (@list Z)) (flat_data_2: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (line: Z) (items_2: (@list (@list Z))) __default__App_option_Z __default__List_Z (PreH1 : (line >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth (k_2) (last_numbers) (0))) /\ ((Znth (k_2) (last_numbers) (0)) <= n_pre)))) (PreH6 : (Pre last_numbers )) (PreH7 : (Spec last_numbers items_2 )) (PreH8 : ((Zlength (items_2)) = n_pre)) (PreH9 : (0 <= line)) (PreH10 : (line <= n_pre)) (PreH11 : (0 <= depth)) (PreH12 : (depth <= line)) (PreH13 : (depth = (Zlength (active)))) (PreH14 : (CurrentItem items_2 line active )) (PreH15 : (BoundedItem n_pre active )) (PreH16 : (total = (Zlength (flat_data_2)))) (PreH17 : (0 <= total)) (PreH18 : (total <= (line * n_pre ))) (PreH19 : (FlatPrefix items_2 line flat_data_2 )) (PreH20 : (LengthsPrefix items_2 line lengths_data_2 )) (PreH21 : ((Zlength (cells)) = 1005)) (PreH22 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < depth)) -> ((Znth k_3 cells __default__App_option_Z) = (Some ((Znth k_3 active 0)))))),
  ((( &( "depth" ) )) # Int  |-> depth)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data_2 )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data_2 )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  EX (lengths_data: (@list Z)) (flat_data: (@list Z)) (items: (@list (@list Z))),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (flat_data = (concat (items))) ”
  &&  “ (total = (Zlength (flat_data))) ”
  &&  “ ((Zlength (lengths_data)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((Znth k lengths_data 0) = (Zlength ((Znth k items __default__List_Z))))) ”
  &&  ((( &( "depth" ) )) # Int  |->_)
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.undef_full ( &( "stack" ) ) 1005 )
  **  (IntArray.full flat_pre total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.full lengths_pre n_pre lengths_data )
) \/
(
forall (last_numbers: (@list Z)) (n_pre: Z) (cells: (@list (@option Z))) (lengths_data_2: (@list Z)) (flat_data_2: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (line: Z) (items_2: (@list (@list Z))) __default__App_option_Z __default__List_Z (PreH1 : (line >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth (k_2) (last_numbers) (0))) /\ ((Znth (k_2) (last_numbers) (0)) <= n_pre)))) (PreH6 : (Pre last_numbers )) (PreH7 : (Spec last_numbers items_2 )) (PreH8 : ((Zlength (items_2)) = n_pre)) (PreH9 : (0 <= line)) (PreH10 : (line <= n_pre)) (PreH11 : (0 <= depth)) (PreH12 : (depth <= line)) (PreH13 : (depth = (Zlength (active)))) (PreH14 : (CurrentItem items_2 line active )) (PreH15 : (BoundedItem n_pre active )) (PreH16 : (total = (Zlength (flat_data_2)))) (PreH17 : (0 <= total)) (PreH18 : (total <= (line * n_pre ))) (PreH19 : (FlatPrefix items_2 line flat_data_2 )) (PreH20 : (LengthsPrefix items_2 line lengths_data_2 )) (PreH21 : ((Zlength (cells)) = 1005)) (PreH22 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < depth)) -> ((Znth k_3 cells __default__App_option_Z) = (Some ((Znth k_3 active 0)))))),
  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
|--
  EX (items: (@list (@list Z))),
  “ (flat_data_2 = (concat (items))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (total = (Zlength ((concat (items))))) ”
  &&  “ ((Zlength (lengths_data_2)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((Znth k lengths_data_2 0) = (Zlength ((Znth k items __default__List_Z))))) ”
  &&  (IntArray.undef_full ( &( "stack" ) ) 1005 )
).

Definition solver_return_wit_1 :=
(
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (items: (@list (@list Z))) (flat_data: (@list Z)) (lengths_data_2: (@list Z)) (total: Z) __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : (Spec last_numbers items )) (PreH5 : ((Zlength (items)) = n_pre)) (PreH6 : (flat_data = (concat (items)))) (PreH7 : (total = (Zlength (flat_data)))) (PreH8 : ((Zlength (lengths_data_2)) = n_pre)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((Znth k lengths_data_2 0) = (Zlength ((Znth k items __default__List_Z)))))),
  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.full flat_pre total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.full lengths_pre n_pre lengths_data_2 )
|--
  EX (lengths_data: (@list Z)) (result: (@list (@list Z))),
  “ (Spec last_numbers result ) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((Znth i lengths_data 0) = (Zlength ((Znth i result __default__List_Z))))) ”
  &&  “ (total = (Zlength ((concat (result))))) ”
  &&  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.full flat_pre (Zlength ((concat (result)))) (concat (result)) )
  **  (IntArray.undef_seg flat_pre (Zlength ((concat (result)))) (n_pre * n_pre ) )
  **  (IntArray.full lengths_pre n_pre lengths_data )
) \/
(
forall (last_numbers: (@list Z)) (n_pre: Z) (flat_pre: Z) (items: (@list (@list Z))) (flat_data: (@list Z)) (lengths_data_2: (@list Z)) (total: Z) __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : (Spec last_numbers items )) (PreH5 : ((Zlength (items)) = n_pre)) (PreH6 : (flat_data = (concat (items)))) (PreH7 : (total = (Zlength (flat_data)))) (PreH8 : ((Zlength (lengths_data_2)) = n_pre)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((Znth k lengths_data_2 0) = (Zlength ((Znth k items __default__List_Z)))))),
  (IntArray.full flat_pre total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
|--
  EX (result: (@list (@list Z))),
  “ (Spec last_numbers result ) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((Znth i lengths_data_2 0) = (Zlength ((Znth i result __default__List_Z))))) ”
  &&  “ (total = (Zlength ((concat (result))))) ”
  &&  (IntArray.full flat_pre (Zlength ((concat (result)))) (concat (result)) )
  **  (IntArray.undef_seg flat_pre (Zlength ((concat (result)))) (n_pre * n_pre ) )
).

Definition solver_partial_solve_wit_1 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : (line < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH6 : (Pre last_numbers )) (PreH7 : (Spec last_numbers items )) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : (0 <= line)) (PreH10 : (line <= n_pre)) (PreH11 : (0 <= depth)) (PreH12 : (depth <= line)) (PreH13 : (depth = (Zlength (active)))) (PreH14 : (CurrentItem items line active )) (PreH15 : (BoundedItem n_pre active )) (PreH16 : (total = (Zlength (flat_data)))) (PreH17 : (0 <= total)) (PreH18 : (total <= (line * n_pre ))) (PreH19 : (FlatPrefix items line flat_data )) (PreH20 : (LengthsPrefix items line lengths_data )) (PreH21 : ((Zlength (cells)) = 1005)) (PreH22 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))),
  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ (line < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 <= line) ”
  &&  “ (line <= n_pre) ”
  &&  “ (0 <= depth) ”
  &&  “ (depth <= line) ”
  &&  “ (depth = (Zlength (active))) ”
  &&  “ (CurrentItem items line active ) ”
  &&  “ (BoundedItem n_pre active ) ”
  &&  “ (total = (Zlength (flat_data))) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= (line * n_pre )) ”
  &&  “ (FlatPrefix items line flat_data ) ”
  &&  “ (LengthsPrefix items line lengths_data ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  (((values_pre + (line * sizeof(INT)))) # Int  |-> (Znth line last_numbers 0))
  **  (IntArray.missing_i values_pre line 0 n_pre last_numbers )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
.

Definition solver_partial_solve_wit_2 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (cells: (@list (@option Z))) (lengths_data: (@list Z)) (flat_data: (@list Z)) (total: Z) (active: (@list Z)) (depth: Z) (line: Z) (items: (@list (@list Z))) __default__App_option_Z (PreH1 : ((Znth line last_numbers 0) = 1)) (PreH2 : (line < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH7 : (Pre last_numbers )) (PreH8 : (Spec last_numbers items )) (PreH9 : ((Zlength (items)) = n_pre)) (PreH10 : (0 <= line)) (PreH11 : (line <= n_pre)) (PreH12 : (0 <= depth)) (PreH13 : (depth <= line)) (PreH14 : (depth = (Zlength (active)))) (PreH15 : (CurrentItem items line active )) (PreH16 : (BoundedItem n_pre active )) (PreH17 : (total = (Zlength (flat_data)))) (PreH18 : (0 <= total)) (PreH19 : (total <= (line * n_pre ))) (PreH20 : (FlatPrefix items line flat_data )) (PreH21 : (LengthsPrefix items line lengths_data )) (PreH22 : ((Zlength (cells)) = 1005)) (PreH23 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))),
  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ ((Znth line last_numbers 0) = 1) ”
  &&  “ (line < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 <= line) ”
  &&  “ (line <= n_pre) ”
  &&  “ (0 <= depth) ”
  &&  “ (depth <= line) ”
  &&  “ (depth = (Zlength (active))) ”
  &&  “ (CurrentItem items line active ) ”
  &&  “ (BoundedItem n_pre active ) ”
  &&  “ (total = (Zlength (flat_data))) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= (line * n_pre )) ”
  &&  “ (FlatPrefix items line flat_data ) ”
  &&  “ (LengthsPrefix items line lengths_data ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  (((( &( "stack" ) ) + (depth * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) depth 0 1005 cells )
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
.

Definition solver_partial_solve_wit_3 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (items: (@list (@list Z))) (cells: (@list (@option Z))) (active: (@list Z)) (flat_data: (@list Z)) (lengths_data: (@list Z)) (line: Z) (depth: Z) (total: Z) __default__App_option_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH5 : (Pre last_numbers )) (PreH6 : (Spec last_numbers items )) (PreH7 : ((Zlength (items)) = n_pre)) (PreH8 : (0 <= line)) (PreH9 : (line < n_pre)) (PreH10 : (active = (Znth (line) (items) ((@nil Z))))) (PreH11 : (1 <= depth)) (PreH12 : (depth <= (line + 1 ))) (PreH13 : (depth = (Zlength (active)))) (PreH14 : (BoundedItem n_pre active )) (PreH15 : (total = (Zlength (flat_data)))) (PreH16 : (0 <= total)) (PreH17 : (total <= (line * n_pre ))) (PreH18 : (FlatPrefix items line flat_data )) (PreH19 : (LengthsPrefix items line lengths_data )) (PreH20 : ((Zlength (cells)) = 1005)) (PreH21 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))),
  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
  **  (IntArray.undef_seg lengths_pre line n_pre )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 <= line) ”
  &&  “ (line < n_pre) ”
  &&  “ (active = (Znth (line) (items) ((@nil Z)))) ”
  &&  “ (1 <= depth) ”
  &&  “ (depth <= (line + 1 )) ”
  &&  “ (depth = (Zlength (active))) ”
  &&  “ (BoundedItem n_pre active ) ”
  &&  “ (total = (Zlength (flat_data))) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= (line * n_pre )) ”
  &&  “ (FlatPrefix items line flat_data ) ”
  &&  “ (LengthsPrefix items line lengths_data ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  (((lengths_pre + (line * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg lengths_pre (line + 1 ) n_pre )
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (IntArray.mixed_full ( &( "stack" ) ) 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 line lengths_data )
.

Definition solver_partial_solve_wit_4 :=
forall (last_numbers: (@list Z)) (values_pre: Z) (n_pre: Z) (flat_pre: Z) (lengths_pre: Z) (items: (@list (@list Z))) (cells: (@list (@option Z))) (active: (@list Z)) (flat_before: (@list Z)) (flat_data: (@list Z)) (lengths_data: (@list Z)) (line: Z) (depth: Z) (i: Z) (total: Z) __default__App_option_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre)))) (PreH5 : (Pre last_numbers )) (PreH6 : (Spec last_numbers items )) (PreH7 : ((Zlength (items)) = n_pre)) (PreH8 : (0 <= line)) (PreH9 : (line < n_pre)) (PreH10 : (active = (Znth (line) (items) ((@nil Z))))) (PreH11 : (1 <= depth)) (PreH12 : (depth <= (line + 1 ))) (PreH13 : ((line + 1 ) <= n_pre)) (PreH14 : (depth = (Zlength (active)))) (PreH15 : (BoundedItem n_pre active )) (PreH16 : (0 <= i)) (PreH17 : (i < depth)) (PreH18 : (FlatPrefix items line flat_before )) (PreH19 : (flat_data = (app (flat_before) ((sublist (0) (i) (active)))))) (PreH20 : (total = (Zlength (flat_data)))) (PreH21 : (0 <= total)) (PreH22 : ((total + (depth - i ) ) <= ((line + 1 ) * n_pre ))) (PreH23 : (((line + 1 ) * n_pre ) <= (n_pre * n_pre ))) (PreH24 : (LengthsPrefix items (line + 1 ) lengths_data )) (PreH25 : ((Zlength (cells)) = 1005)) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0)))))) (PreH27 : ((Znth i cells __default__App_option_Z) = (Some ((Znth i active 0))))),
  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth i active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) i 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.undef_seg flat_pre total (n_pre * n_pre ) )
  **  (IntArray.seg lengths_pre 0 (line + 1 ) lengths_data )
  **  (IntArray.undef_seg lengths_pre (line + 1 ) n_pre )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000) ”
  &&  “ (n_pre = (Zlength (last_numbers))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) (0))) /\ ((Znth (k) (last_numbers) (0)) <= n_pre))) ”
  &&  “ (Pre last_numbers ) ”
  &&  “ (Spec last_numbers items ) ”
  &&  “ ((Zlength (items)) = n_pre) ”
  &&  “ (0 <= line) ”
  &&  “ (line < n_pre) ”
  &&  “ (active = (Znth (line) (items) ((@nil Z)))) ”
  &&  “ (1 <= depth) ”
  &&  “ (depth <= (line + 1 )) ”
  &&  “ ((line + 1 ) <= n_pre) ”
  &&  “ (depth = (Zlength (active))) ”
  &&  “ (BoundedItem n_pre active ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < depth) ”
  &&  “ (FlatPrefix items line flat_before ) ”
  &&  “ (flat_data = (app (flat_before) ((sublist (0) (i) (active))))) ”
  &&  “ (total = (Zlength (flat_data))) ”
  &&  “ (0 <= total) ”
  &&  “ ((total + (depth - i ) ) <= ((line + 1 ) * n_pre )) ”
  &&  “ (((line + 1 ) * n_pre ) <= (n_pre * n_pre )) ”
  &&  “ (LengthsPrefix items (line + 1 ) lengths_data ) ”
  &&  “ ((Zlength (cells)) = 1005) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active 0))))) ”
  &&  “ ((Znth i cells __default__App_option_Z) = (Some ((Znth i active 0)))) ”
  &&  (((flat_pre + (total * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg flat_pre (total + 1 ) (n_pre * n_pre ) )
  **  (IntArray.full values_pre n_pre last_numbers )
  **  (((( &( "stack" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth i active 0))
  **  (IntArray.mixed_missing_i ( &( "stack" ) ) i 0 1005 cells )
  **  (IntArray.seg flat_pre 0 total flat_data )
  **  (IntArray.seg lengths_pre 0 (line + 1 ) lengths_data )
  **  (IntArray.undef_seg lengths_pre (line + 1 ) n_pre )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.

End VC_Correct.
