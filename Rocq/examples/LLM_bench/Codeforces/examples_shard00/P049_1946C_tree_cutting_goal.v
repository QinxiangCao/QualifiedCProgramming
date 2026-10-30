From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P049_1946C_tree_cutting_lib.
Local Open Scope sac.

(*----- Function feasible -----*)

Definition feasible_safety_wit_1 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (PreH1 : (1 <= minimum_pre)) (PreH2 : (minimum_pre <= nv)) (PreH3 : (1 <= kv)) (PreH4 : (kv < nv)) (PreH5 : (nv <= 100000)) (PreH6 : (Pre nv kv edges )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH8 : (RootedOrderModel nv edges parent_data order_data )) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_2 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (i: Z) (initialized: (@list Z)) (PreH1 : (i < nv)) (PreH2 : (1 <= minimum_pre)) (PreH3 : (minimum_pre <= nv)) (PreH4 : (SizeInitializationState nv i initialized )) (PreH5 : (Pre nv kv edges )) (PreH6 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH7 : (RootedOrderModel nv edges parent_data order_data )) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))),
  (IntArray.seg size_p 0 (i + 1 ) (app (initialized) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg size_p (i + 1 ) nv )
  **  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition feasible_safety_wit_3 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (i: Z) (initialized: (@list Z)) (PreH1 : (i < nv)) (PreH2 : (1 <= minimum_pre)) (PreH3 : (minimum_pre <= nv)) (PreH4 : (SizeInitializationState nv i initialized )) (PreH5 : (Pre nv kv edges )) (PreH6 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH7 : (RootedOrderModel nv edges parent_data order_data )) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))),
  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.seg size_p 0 i initialized )
  **  (IntArray.undef_seg size_p i nv )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition feasible_safety_wit_4 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (i: Z) (initialized: (@list Z)) (PreH1 : (i >= nv)) (PreH2 : (1 <= minimum_pre)) (PreH3 : (minimum_pre <= nv)) (PreH4 : (SizeInitializationState nv i initialized )) (PreH5 : (Pre nv kv edges )) (PreH6 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH7 : (RootedOrderModel nv edges parent_data order_data )) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))),
  ((( &( "components" ) )) # Int  |->_)
  **  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.seg size_p 0 i initialized )
  **  (IntArray.undef_seg size_p i nv )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_5 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (i: Z) (initialized: (@list Z)) (PreH1 : (i >= nv)) (PreH2 : (1 <= minimum_pre)) (PreH3 : (minimum_pre <= nv)) (PreH4 : (SizeInitializationState nv i initialized )) (PreH5 : (Pre nv kv edges )) (PreH6 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH7 : (RootedOrderModel nv edges parent_data order_data )) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))),
  ((( &( "oi" ) )) # Int  |->_)
  **  ((( &( "components" ) )) # Int  |-> 0)
  **  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.seg size_p 0 i initialized )
  **  (IntArray.undef_seg size_p i nv )
|--
  “ ((nv - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (nv - 1 )) ”
.

Definition feasible_safety_wit_6 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (i: Z) (initialized: (@list Z)) (PreH1 : (i >= nv)) (PreH2 : (1 <= minimum_pre)) (PreH3 : (minimum_pre <= nv)) (PreH4 : (SizeInitializationState nv i initialized )) (PreH5 : (Pre nv kv edges )) (PreH6 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH7 : (RootedOrderModel nv edges parent_data order_data )) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))),
  ((( &( "oi" ) )) # Int  |->_)
  **  ((( &( "components" ) )) # Int  |-> 0)
  **  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.seg size_p 0 i initialized )
  **  (IntArray.undef_seg size_p i nv )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition feasible_safety_wit_7 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : (1 <= minimum_pre)) (PreH2 : (minimum_pre <= nv)) (PreH3 : ((-1) <= oi)) (PreH4 : (oi < nv)) (PreH5 : (0 <= components)) (PreH6 : (components <= ((nv - 1 ) - oi ))) (PreH7 : ((Zlength (sizes)) = nv)) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH9 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH10 : (Pre nv kv edges )) (PreH11 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH12 : (RootedOrderModel nv edges parent_data order_data )) (PreH13 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH14 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "oi" ) )) # Int  |-> oi)
  **  ((( &( "components" ) )) # Int  |-> components)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.full size_p nv sizes )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_8 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre)) (PreH2 : (oi >= 0)) (PreH3 : (1 <= minimum_pre)) (PreH4 : (minimum_pre <= nv)) (PreH5 : ((-1) <= oi)) (PreH6 : (oi < nv)) (PreH7 : (0 <= components)) (PreH8 : (components <= ((nv - 1 ) - oi ))) (PreH9 : ((Zlength (sizes)) = nv)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH11 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH12 : (Pre nv kv edges )) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (RootedOrderModel nv edges parent_data order_data )) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH16 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv sizes )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth oi order_data 0))
  **  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "oi" ) )) # Int  |-> oi)
  **  ((( &( "components" ) )) # Int  |-> components)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
|--
  “ ((components + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (components + 1 )) ”
.

Definition feasible_safety_wit_9 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre)) (PreH2 : (oi >= 0)) (PreH3 : (1 <= minimum_pre)) (PreH4 : (minimum_pre <= nv)) (PreH5 : ((-1) <= oi)) (PreH6 : (oi < nv)) (PreH7 : (0 <= components)) (PreH8 : (components <= ((nv - 1 ) - oi ))) (PreH9 : ((Zlength (sizes)) = nv)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH11 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH12 : (Pre nv kv edges )) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (RootedOrderModel nv edges parent_data order_data )) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH16 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv sizes )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth oi order_data 0))
  **  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "oi" ) )) # Int  |-> oi)
  **  ((( &( "components" ) )) # Int  |-> (components + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_10 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre)) (PreH2 : (oi >= 0)) (PreH3 : (1 <= minimum_pre)) (PreH4 : (minimum_pre <= nv)) (PreH5 : ((-1) <= oi)) (PreH6 : (oi < nv)) (PreH7 : (0 <= components)) (PreH8 : (components <= ((nv - 1 ) - oi ))) (PreH9 : ((Zlength (sizes)) = nv)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH11 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH12 : (Pre nv kv edges )) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (RootedOrderModel nv edges parent_data order_data )) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH16 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full size_p nv (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth oi order_data 0))
  **  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "oi" ) )) # Int  |-> oi)
  **  ((( &( "components" ) )) # Int  |-> (components + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_11 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) sizes 0) < minimum_pre)) (PreH2 : (oi >= 0)) (PreH3 : (1 <= minimum_pre)) (PreH4 : (minimum_pre <= nv)) (PreH5 : ((-1) <= oi)) (PreH6 : (oi < nv)) (PreH7 : (0 <= components)) (PreH8 : (components <= ((nv - 1 ) - oi ))) (PreH9 : ((Zlength (sizes)) = nv)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH11 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH12 : (Pre nv kv edges )) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (RootedOrderModel nv edges parent_data order_data )) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH16 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full size_p nv sizes )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth oi order_data 0))
  **  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "oi" ) )) # Int  |-> oi)
  **  ((( &( "components" ) )) # Int  |-> components)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition feasible_safety_wit_12 :=
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth oi order_data 0))
  **  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "oi" ) )) # Int  |-> oi)
  **  ((( &( "components" ) )) # Int  |-> (components + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (((Znth (Znth (Znth oi order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) 0) + (Znth (Znth oi order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) 0) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (Znth (Znth oi order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) 0) + (Znth (Znth oi order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) 0) )) ”
) \/
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth oi order_data 0))
  **  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "oi" ) )) # Int  |-> oi)
  **  ((( &( "components" ) )) # Int  |-> (components + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (((Znth (Znth (Znth oi order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) 0) + (Znth (Znth oi order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) 0) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (Znth (Znth oi order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) 0) + (Znth (Znth oi order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) 0) )) ”
).

Definition feasible_safety_wit_12_split_goal_1 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth oi order_data 0))
  **  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "oi" ) )) # Int  |-> oi)
  **  ((( &( "components" ) )) # Int  |-> (components + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (((Znth (Znth (Znth oi order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) 0) + (Znth (Znth oi order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) 0) ) <= INT_MAX) ”
.

Definition feasible_safety_wit_12_split_goal_2 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth oi order_data 0))
  **  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "oi" ) )) # Int  |-> oi)
  **  ((( &( "components" ) )) # Int  |-> (components + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ ((INT_MIN) <= ((Znth (Znth (Znth oi order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) 0) + (Znth (Znth oi order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) 0) )) ”
.

Definition feasible_safety_wit_13 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes 0) < minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv sizes )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth oi order_data 0))
  **  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "oi" ) )) # Int  |-> oi)
  **  ((( &( "components" ) )) # Int  |-> components)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) )) ”
.

Definition feasible_safety_wit_14 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv (replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) 0) + (Znth (Znth oi order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) 0) )) ((replace_Znth ((Znth oi order_data 0)) (0) (sizes)))) )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "oi" ) )) # Int  |-> oi)
  **  ((( &( "components" ) )) # Int  |-> (components + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ ((oi - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (oi - 1 )) ”
.

Definition feasible_safety_wit_15 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes 0) < minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv (replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) )) (sizes)) )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "oi" ) )) # Int  |-> oi)
  **  ((( &( "components" ) )) # Int  |-> components)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ ((oi - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (oi - 1 )) ”
.

Definition feasible_safety_wit_16 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) < 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full size_p nv (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "oi" ) )) # Int  |-> oi)
  **  ((( &( "components" ) )) # Int  |-> (components + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ ((oi - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (oi - 1 )) ”
.

Definition feasible_safety_wit_17 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) < 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes 0) < minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full size_p nv sizes )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "oi" ) )) # Int  |-> oi)
  **  ((( &( "components" ) )) # Int  |-> components)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ ((oi - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (oi - 1 )) ”
.

Definition feasible_safety_wit_18 :=
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : (oi < 0)) (PreH2 : (1 <= minimum_pre)) (PreH3 : (minimum_pre <= nv)) (PreH4 : ((-1) <= oi)) (PreH5 : (oi < nv)) (PreH6 : (0 <= components)) (PreH7 : (components <= ((nv - 1 ) - oi ))) (PreH8 : ((Zlength (sizes)) = nv)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH10 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH11 : (Pre nv kv edges )) (PreH12 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH13 : (RootedOrderModel nv edges parent_data order_data )) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH15 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "components" ) )) # Int  |-> components)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.full size_p nv sizes )
|--
  “ ((kv + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (kv + 1 )) ”
) \/
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : (oi < 0)) (PreH2 : (1 <= minimum_pre)) (PreH3 : (minimum_pre <= nv)) (PreH4 : ((-1) <= oi)) (PreH5 : (oi < nv)) (PreH6 : (0 <= components)) (PreH7 : (components <= ((nv - 1 ) - oi ))) (PreH8 : ((Zlength (sizes)) = nv)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH10 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH11 : (Pre nv kv edges )) (PreH12 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH13 : (RootedOrderModel nv edges parent_data order_data )) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH15 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "components" ) )) # Int  |-> components)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.full size_p nv sizes )
|--
  “ ((kv + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (kv + 1 )) ”
).

Definition feasible_safety_wit_18_split_goal_1 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : (oi < 0)) (PreH2 : (1 <= minimum_pre)) (PreH3 : (minimum_pre <= nv)) (PreH4 : ((-1) <= oi)) (PreH5 : (oi < nv)) (PreH6 : (0 <= components)) (PreH7 : (components <= ((nv - 1 ) - oi ))) (PreH8 : ((Zlength (sizes)) = nv)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH10 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH11 : (Pre nv kv edges )) (PreH12 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH13 : (RootedOrderModel nv edges parent_data order_data )) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH15 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "components" ) )) # Int  |-> components)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.full size_p nv sizes )
|--
  “ ((kv + 1 ) <= INT_MAX) ”
.

Definition feasible_safety_wit_18_split_goal_2 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : (oi < 0)) (PreH2 : (1 <= minimum_pre)) (PreH3 : (minimum_pre <= nv)) (PreH4 : ((-1) <= oi)) (PreH5 : (oi < nv)) (PreH6 : (0 <= components)) (PreH7 : (components <= ((nv - 1 ) - oi ))) (PreH8 : ((Zlength (sizes)) = nv)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH10 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH11 : (Pre nv kv edges )) (PreH12 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH13 : (RootedOrderModel nv edges parent_data order_data )) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH15 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "components" ) )) # Int  |-> components)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.full size_p nv sizes )
|--
  “ ((INT_MIN) <= (kv + 1 )) ”
.

Definition feasible_safety_wit_19 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : (oi < 0)) (PreH2 : (1 <= minimum_pre)) (PreH3 : (minimum_pre <= nv)) (PreH4 : ((-1) <= oi)) (PreH5 : (oi < nv)) (PreH6 : (0 <= components)) (PreH7 : (components <= ((nv - 1 ) - oi ))) (PreH8 : ((Zlength (sizes)) = nv)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH10 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH11 : (Pre nv kv edges )) (PreH12 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH13 : (RootedOrderModel nv edges parent_data order_data )) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH15 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  ((( &( "minimum" ) )) # Int  |-> minimum_pre)
  **  ((( &( "components" ) )) # Int  |-> components)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.full size_p nv sizes )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition feasible_entail_wit_1 :=
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (PreH1 : (1 <= minimum_pre)) (PreH2 : (minimum_pre <= nv)) (PreH3 : (1 <= kv)) (PreH4 : (kv < nv)) (PreH5 : (nv <= 100000)) (PreH6 : (Pre nv kv edges )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH8 : (RootedOrderModel nv edges parent_data order_data )) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  EX (initialized: (@list Z)),
  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ (SizeInitializationState nv 0 initialized ) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.seg size_p 0 0 initialized )
  **  (IntArray.undef_seg size_p 0 nv )
) \/
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (PreH1 : (1 <= minimum_pre)) (PreH2 : (minimum_pre <= nv)) (PreH3 : (1 <= kv)) (PreH4 : (kv < nv)) (PreH5 : (nv <= 100000)) (PreH6 : (Pre nv kv edges )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH8 : (RootedOrderModel nv edges parent_data order_data )) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))),
  TT && emp 
|--
  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
  &&  “ (SizeInitializationState nv 0 (@nil Z) ) ”
  &&  emp
).

Definition feasible_entail_wit_1_split_goal_1 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (PreH1 : (1 <= minimum_pre)) (PreH2 : (minimum_pre <= nv)) (PreH3 : (1 <= kv)) (PreH4 : (kv < nv)) (PreH5 : (nv <= 100000)) (PreH6 : (Pre nv kv edges )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH8 : (RootedOrderModel nv edges parent_data order_data )) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))),
  forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))
.

Definition feasible_entail_wit_1_split_goal_2 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (PreH1 : (1 <= minimum_pre)) (PreH2 : (minimum_pre <= nv)) (PreH3 : (1 <= kv)) (PreH4 : (kv < nv)) (PreH5 : (nv <= 100000)) (PreH6 : (Pre nv kv edges )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH8 : (RootedOrderModel nv edges parent_data order_data )) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))),
  (SizeInitializationState nv 0 (@nil Z) )
.

Definition feasible_entail_wit_2 :=
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (i: Z) (initialized_2: (@list Z)) (PreH1 : (i < nv)) (PreH2 : (1 <= minimum_pre)) (PreH3 : (minimum_pre <= nv)) (PreH4 : (SizeInitializationState nv i initialized_2 )) (PreH5 : (Pre nv kv edges )) (PreH6 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH7 : (RootedOrderModel nv edges parent_data order_data )) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))),
  (IntArray.seg size_p 0 (i + 1 ) (app (initialized_2) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg size_p (i + 1 ) nv )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
|--
  EX (initialized: (@list Z)),
  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ (SizeInitializationState nv (i + 1 ) initialized ) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.seg size_p 0 (i + 1 ) initialized )
  **  (IntArray.undef_seg size_p (i + 1 ) nv )
) \/
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (i: Z) (initialized_2: (@list Z)) (PreH1 : (i < nv)) (PreH2 : (1 <= minimum_pre)) (PreH3 : (minimum_pre <= nv)) (PreH4 : (SizeInitializationState nv i initialized_2 )) (PreH5 : (Pre nv kv edges )) (PreH6 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH7 : (RootedOrderModel nv edges parent_data order_data )) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))),
  TT && emp 
|--
  “ (SizeInitializationState nv (i + 1 ) (app (initialized_2) ((cons (1) ((@nil Z))))) ) ”
  &&  emp
).

Definition feasible_entail_wit_2_split_goal_1 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (i: Z) (initialized_2: (@list Z)) (PreH1 : (i < nv)) (PreH2 : (1 <= minimum_pre)) (PreH3 : (minimum_pre <= nv)) (PreH4 : (SizeInitializationState nv i initialized_2 )) (PreH5 : (Pre nv kv edges )) (PreH6 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH7 : (RootedOrderModel nv edges parent_data order_data )) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))),
  (SizeInitializationState nv (i + 1 ) (app (initialized_2) ((cons (1) ((@nil Z))))) )
.

Definition feasible_entail_wit_3 :=
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (i: Z) (initialized: (@list Z)) (PreH1 : (i >= nv)) (PreH2 : (1 <= minimum_pre)) (PreH3 : (minimum_pre <= nv)) (PreH4 : (SizeInitializationState nv i initialized )) (PreH5 : (Pre nv kv edges )) (PreH6 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH7 : (RootedOrderModel nv edges parent_data order_data )) (PreH8 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < nv)) -> ((((0 <= (Znth j_3 order_data 0)) /\ ((Znth j_3 order_data 0) < nv)) /\ ((-1) <= (Znth j_3 parent_data 0))) /\ ((Znth j_3 parent_data 0) < nv)))),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.seg size_p 0 i initialized )
  **  (IntArray.undef_seg size_p i nv )
|--
  EX (sizes: (@list Z)),
  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= (nv - 1 )) ”
  &&  “ ((nv - 1 ) < nv) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= ((nv - 1 ) - (nv - 1 ) )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ ((((nv - 1 ) >= 0) /\ ((Znth (Znth (nv - 1 ) order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth (nv - 1 ) order_data 0) parent_data 0) sizes 0) + (Znth (Znth (nv - 1 ) order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre (nv - 1 ) 0 parent_data order_data sizes ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.full size_p nv sizes )
) \/
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (i: Z) (initialized: (@list Z)) (PreH1 : (i >= nv)) (PreH2 : (1 <= minimum_pre)) (PreH3 : (minimum_pre <= nv)) (PreH4 : (SizeInitializationState nv i initialized )) (PreH5 : (Pre nv kv edges )) (PreH6 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH7 : (RootedOrderModel nv edges parent_data order_data )) (PreH8 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < nv)) -> ((((0 <= (Znth j_3 order_data 0)) /\ ((Znth j_3 order_data 0) < nv)) /\ ((-1) <= (Znth j_3 parent_data 0))) /\ ((Znth j_3 parent_data 0) < nv)))),
  (IntArray.seg size_p 0 i initialized )
  **  (IntArray.undef_seg size_p i nv )
|--
  EX (sizes: (@list Z)),
  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= (nv - 1 )) ”
  &&  “ ((nv - 1 ) < nv) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= ((nv - 1 ) - (nv - 1 ) )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ ((((nv - 1 ) >= 0) /\ ((Znth (Znth (nv - 1 ) order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth (nv - 1 ) order_data 0) parent_data 0) sizes 0) + (Znth (Znth (nv - 1 ) order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre (nv - 1 ) 0 parent_data order_data sizes ) ”
  &&  (IntArray.full size_p nv sizes )
).

Definition feasible_entail_wit_4_1 :=
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  (IntArray.full size_p nv (replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) + (Znth (Znth oi order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) )) ((replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)))) )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  EX (sizes: (@list Z)),
  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= (oi - 1 )) ”
  &&  “ ((oi - 1 ) < nv) ”
  &&  “ (0 <= (components + 1 )) ”
  &&  “ ((components + 1 ) <= ((nv - 1 ) - (oi - 1 ) )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ ((((oi - 1 ) >= 0) /\ ((Znth (Znth (oi - 1 ) order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth (oi - 1 ) order_data 0) parent_data 0) sizes 0) + (Znth (Znth (oi - 1 ) order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre (oi - 1 ) (components + 1 ) parent_data order_data sizes ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.full size_p nv sizes )
) \/
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  TT && emp 
|--
  “ (CutScanState nv kv edges minimum_pre (oi - 1 ) (components + 1 ) parent_data order_data (replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) + (Znth (Znth oi order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) )) ((replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)))) ) ”
  &&  “ ((((oi - 1 ) >= 0) /\ ((Znth (Znth (oi - 1 ) order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth (oi - 1 ) order_data 0) parent_data 0) (replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) + (Znth (Znth oi order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) )) ((replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)))) 0) + (Znth (Znth (oi - 1 ) order_data 0) (replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) + (Znth (Znth oi order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) )) ((replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)))) 0) ) <= nv)) ”
  &&  “ ((Zlength ((replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) + (Znth (Znth oi order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) )) ((replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)))))) = nv) ”
  &&  emp
).

Definition feasible_entail_wit_4_1_split_goal_1 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  (CutScanState nv kv edges minimum_pre (oi - 1 ) (components + 1 ) parent_data order_data (replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) + (Znth (Znth oi order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) )) ((replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)))) )
.

Definition feasible_entail_wit_4_1_split_goal_2 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  ((((oi - 1 ) >= 0) /\ ((Znth (Znth (oi - 1 ) order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth (oi - 1 ) order_data 0) parent_data 0) (replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) + (Znth (Znth oi order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) )) ((replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)))) 0) + (Znth (Znth (oi - 1 ) order_data 0) (replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) + (Znth (Znth oi order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) )) ((replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)))) 0) ) <= nv))
.

Definition feasible_entail_wit_4_1_split_goal_3 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  ((Zlength ((replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) + (Znth (Znth oi order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) )) ((replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)))))) = nv)
.

Definition feasible_entail_wit_4_2 :=
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) < minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  (IntArray.full size_p nv (replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) )) (sizes_2)) )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  EX (sizes: (@list Z)),
  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= (oi - 1 )) ”
  &&  “ ((oi - 1 ) < nv) ”
  &&  “ (0 <= components) ”
  &&  “ (components <= ((nv - 1 ) - (oi - 1 ) )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ ((((oi - 1 ) >= 0) /\ ((Znth (Znth (oi - 1 ) order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth (oi - 1 ) order_data 0) parent_data 0) sizes 0) + (Znth (Znth (oi - 1 ) order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre (oi - 1 ) components parent_data order_data sizes ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.full size_p nv sizes )
) \/
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) < minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  TT && emp 
|--
  “ (CutScanState nv kv edges minimum_pre (oi - 1 ) components parent_data order_data (replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) )) (sizes_2)) ) ”
  &&  “ ((((oi - 1 ) >= 0) /\ ((Znth (Znth (oi - 1 ) order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth (oi - 1 ) order_data 0) parent_data 0) (replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) )) (sizes_2)) 0) + (Znth (Znth (oi - 1 ) order_data 0) (replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) )) (sizes_2)) 0) ) <= nv)) ”
  &&  “ ((Zlength ((replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) )) (sizes_2)))) = nv) ”
  &&  emp
).

Definition feasible_entail_wit_4_2_split_goal_1 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) < minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  (CutScanState nv kv edges minimum_pre (oi - 1 ) components parent_data order_data (replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) )) (sizes_2)) )
.

Definition feasible_entail_wit_4_2_split_goal_2 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) < minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  ((((oi - 1 ) >= 0) /\ ((Znth (Znth (oi - 1 ) order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth (oi - 1 ) order_data 0) parent_data 0) (replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) )) (sizes_2)) 0) + (Znth (Znth (oi - 1 ) order_data 0) (replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) )) (sizes_2)) 0) ) <= nv))
.

Definition feasible_entail_wit_4_2_split_goal_3 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) < minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  ((Zlength ((replace_Znth ((Znth (Znth oi order_data 0) parent_data 0)) (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) )) (sizes_2)))) = nv)
.

Definition feasible_entail_wit_4_3 :=
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) < 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full size_p nv (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  EX (sizes: (@list Z)),
  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= (oi - 1 )) ”
  &&  “ ((oi - 1 ) < nv) ”
  &&  “ (0 <= (components + 1 )) ”
  &&  “ ((components + 1 ) <= ((nv - 1 ) - (oi - 1 ) )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ ((((oi - 1 ) >= 0) /\ ((Znth (Znth (oi - 1 ) order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth (oi - 1 ) order_data 0) parent_data 0) sizes 0) + (Znth (Znth (oi - 1 ) order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre (oi - 1 ) (components + 1 ) parent_data order_data sizes ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.full size_p nv sizes )
) \/
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) < 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  TT && emp 
|--
  “ (CutScanState nv kv edges minimum_pre (oi - 1 ) (components + 1 ) parent_data order_data (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) ) ”
  &&  “ ((((oi - 1 ) >= 0) /\ ((Znth (Znth (oi - 1 ) order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth (oi - 1 ) order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) + (Znth (Znth (oi - 1 ) order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) ) <= nv)) ”
  &&  “ ((Zlength ((replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)))) = nv) ”
  &&  emp
).

Definition feasible_entail_wit_4_3_split_goal_1 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) < 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  (CutScanState nv kv edges minimum_pre (oi - 1 ) (components + 1 ) parent_data order_data (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) )
.

Definition feasible_entail_wit_4_3_split_goal_2 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) < 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  ((((oi - 1 ) >= 0) /\ ((Znth (Znth (oi - 1 ) order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth (oi - 1 ) order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) + (Znth (Znth (oi - 1 ) order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)) 0) ) <= nv))
.

Definition feasible_entail_wit_4_3_split_goal_3 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) < 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  ((Zlength ((replace_Znth ((Znth oi order_data 0)) (0) (sizes_2)))) = nv)
.

Definition feasible_entail_wit_4_4 :=
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) < 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) < minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full size_p nv sizes_2 )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  EX (sizes: (@list Z)),
  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= (oi - 1 )) ”
  &&  “ ((oi - 1 ) < nv) ”
  &&  “ (0 <= components) ”
  &&  “ (components <= ((nv - 1 ) - (oi - 1 ) )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ ((((oi - 1 ) >= 0) /\ ((Znth (Znth (oi - 1 ) order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth (oi - 1 ) order_data 0) parent_data 0) sizes 0) + (Znth (Znth (oi - 1 ) order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre (oi - 1 ) components parent_data order_data sizes ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.full size_p nv sizes )
) \/
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) < 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) < minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  TT && emp 
|--
  “ (CutScanState nv kv edges minimum_pre (oi - 1 ) components parent_data order_data sizes_2 ) ”
  &&  “ ((((oi - 1 ) >= 0) /\ ((Znth (Znth (oi - 1 ) order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth (oi - 1 ) order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth (oi - 1 ) order_data 0) sizes_2 0) ) <= nv)) ”
  &&  emp
).

Definition feasible_entail_wit_4_4_split_goal_1 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) < 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) < minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  (CutScanState nv kv edges minimum_pre (oi - 1 ) components parent_data order_data sizes_2 )
.

Definition feasible_entail_wit_4_4_split_goal_2 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes_2: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) < 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes_2 0) < minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes_2)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes_2 0)) /\ ((Znth j sizes_2 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth oi order_data 0) sizes_2 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes_2 )),
  ((((oi - 1 ) >= 0) /\ ((Znth (Znth (oi - 1 ) order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth (oi - 1 ) order_data 0) parent_data 0) sizes_2 0) + (Znth (Znth (oi - 1 ) order_data 0) sizes_2 0) ) <= nv))
.

Definition feasible_return_wit_1 :=
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : (components < (kv + 1 ))) (PreH2 : (oi < 0)) (PreH3 : (1 <= minimum_pre)) (PreH4 : (minimum_pre <= nv)) (PreH5 : ((-1) <= oi)) (PreH6 : (oi < nv)) (PreH7 : (0 <= components)) (PreH8 : (components <= ((nv - 1 ) - oi ))) (PreH9 : ((Zlength (sizes)) = nv)) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((0 <= (Znth j_2 sizes 0)) /\ ((Znth j_2 sizes 0) <= nv)))) (PreH11 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH12 : (Pre nv kv edges )) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (RootedOrderModel nv edges parent_data order_data )) (PreH15 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < nv)) -> ((((0 <= (Znth j_3 order_data 0)) /\ ((Znth j_3 order_data 0) < nv)) /\ ((-1) <= (Znth j_3 parent_data 0))) /\ ((Znth j_3 parent_data 0) < nv)))) (PreH16 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.full size_p nv sizes )
|--
  “ (0 <= 0) ”
  &&  “ (0 <= 1) ”
  &&  “ ((0 <> 0) <-> (ThresholdFeasible nv kv edges minimum_pre )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
) \/
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : (components < (kv + 1 ))) (PreH2 : (oi < 0)) (PreH3 : (1 <= minimum_pre)) (PreH4 : (minimum_pre <= nv)) (PreH5 : ((-1) <= oi)) (PreH6 : (oi < nv)) (PreH7 : (0 <= components)) (PreH8 : (components <= ((nv - 1 ) - oi ))) (PreH9 : ((Zlength (sizes)) = nv)) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((0 <= (Znth j_2 sizes 0)) /\ ((Znth j_2 sizes 0) <= nv)))) (PreH11 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH12 : (Pre nv kv edges )) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (RootedOrderModel nv edges parent_data order_data )) (PreH15 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < nv)) -> ((((0 <= (Znth j_3 order_data 0)) /\ ((Znth j_3 order_data 0) < nv)) /\ ((-1) <= (Znth j_3 parent_data 0))) /\ ((Znth j_3 parent_data 0) < nv)))) (PreH16 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv sizes )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
  &&  “ ((0 <> 0) <-> (ThresholdFeasible nv kv edges minimum_pre )) ”
  &&  (IntArray.undef_full size_p nv )
).

Definition feasible_return_wit_1_split_goal_1 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : (components < (kv + 1 ))) (PreH2 : (oi < 0)) (PreH3 : (1 <= minimum_pre)) (PreH4 : (minimum_pre <= nv)) (PreH5 : ((-1) <= oi)) (PreH6 : (oi < nv)) (PreH7 : (0 <= components)) (PreH8 : (components <= ((nv - 1 ) - oi ))) (PreH9 : ((Zlength (sizes)) = nv)) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((0 <= (Znth j_2 sizes 0)) /\ ((Znth j_2 sizes 0) <= nv)))) (PreH11 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH12 : (Pre nv kv edges )) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (RootedOrderModel nv edges parent_data order_data )) (PreH15 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < nv)) -> ((((0 <= (Znth j_3 order_data 0)) /\ ((Znth j_3 order_data 0) < nv)) /\ ((-1) <= (Znth j_3 parent_data 0))) /\ ((Znth j_3 parent_data 0) < nv)))) (PreH16 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv sizes )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
.

Definition feasible_return_wit_1_split_goal_2 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : (components < (kv + 1 ))) (PreH2 : (oi < 0)) (PreH3 : (1 <= minimum_pre)) (PreH4 : (minimum_pre <= nv)) (PreH5 : ((-1) <= oi)) (PreH6 : (oi < nv)) (PreH7 : (0 <= components)) (PreH8 : (components <= ((nv - 1 ) - oi ))) (PreH9 : ((Zlength (sizes)) = nv)) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((0 <= (Znth j_2 sizes 0)) /\ ((Znth j_2 sizes 0) <= nv)))) (PreH11 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH12 : (Pre nv kv edges )) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (RootedOrderModel nv edges parent_data order_data )) (PreH15 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < nv)) -> ((((0 <= (Znth j_3 order_data 0)) /\ ((Znth j_3 order_data 0) < nv)) /\ ((-1) <= (Znth j_3 parent_data 0))) /\ ((Znth j_3 parent_data 0) < nv)))) (PreH16 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv sizes )
|--
  “ ((0 <> 0) <-> (ThresholdFeasible nv kv edges minimum_pre )) ”
.

Definition feasible_return_wit_1_split_goal_spatial :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : (components < (kv + 1 ))) (PreH2 : (oi < 0)) (PreH3 : (1 <= minimum_pre)) (PreH4 : (minimum_pre <= nv)) (PreH5 : ((-1) <= oi)) (PreH6 : (oi < nv)) (PreH7 : (0 <= components)) (PreH8 : (components <= ((nv - 1 ) - oi ))) (PreH9 : ((Zlength (sizes)) = nv)) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((0 <= (Znth j_2 sizes 0)) /\ ((Znth j_2 sizes 0) <= nv)))) (PreH11 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH12 : (Pre nv kv edges )) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (RootedOrderModel nv edges parent_data order_data )) (PreH15 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < nv)) -> ((((0 <= (Znth j_3 order_data 0)) /\ ((Znth j_3 order_data 0) < nv)) /\ ((-1) <= (Znth j_3 parent_data 0))) /\ ((Znth j_3 parent_data 0) < nv)))) (PreH16 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv sizes )
|--
  (IntArray.undef_full size_p nv )
.

Definition feasible_return_wit_2 :=
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : (components >= (kv + 1 ))) (PreH2 : (oi < 0)) (PreH3 : (1 <= minimum_pre)) (PreH4 : (minimum_pre <= nv)) (PreH5 : ((-1) <= oi)) (PreH6 : (oi < nv)) (PreH7 : (0 <= components)) (PreH8 : (components <= ((nv - 1 ) - oi ))) (PreH9 : ((Zlength (sizes)) = nv)) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((0 <= (Znth j_2 sizes 0)) /\ ((Znth j_2 sizes 0) <= nv)))) (PreH11 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH12 : (Pre nv kv edges )) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (RootedOrderModel nv edges parent_data order_data )) (PreH15 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < nv)) -> ((((0 <= (Znth j_3 order_data 0)) /\ ((Znth j_3 order_data 0) < nv)) /\ ((-1) <= (Znth j_3 parent_data 0))) /\ ((Znth j_3 parent_data 0) < nv)))) (PreH16 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.full size_p nv sizes )
|--
  “ (0 <= 1) ”
  &&  “ (1 <= 1) ”
  &&  “ ((1 <> 0) <-> (ThresholdFeasible nv kv edges minimum_pre )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
) \/
(
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : (components >= (kv + 1 ))) (PreH2 : (oi < 0)) (PreH3 : (1 <= minimum_pre)) (PreH4 : (minimum_pre <= nv)) (PreH5 : ((-1) <= oi)) (PreH6 : (oi < nv)) (PreH7 : (0 <= components)) (PreH8 : (components <= ((nv - 1 ) - oi ))) (PreH9 : ((Zlength (sizes)) = nv)) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((0 <= (Znth j_2 sizes 0)) /\ ((Znth j_2 sizes 0) <= nv)))) (PreH11 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH12 : (Pre nv kv edges )) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (RootedOrderModel nv edges parent_data order_data )) (PreH15 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < nv)) -> ((((0 <= (Znth j_3 order_data 0)) /\ ((Znth j_3 order_data 0) < nv)) /\ ((-1) <= (Znth j_3 parent_data 0))) /\ ((Znth j_3 parent_data 0) < nv)))) (PreH16 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv sizes )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
  &&  “ ((1 <> 0) <-> (ThresholdFeasible nv kv edges minimum_pre )) ”
  &&  (IntArray.undef_full size_p nv )
).

Definition feasible_return_wit_2_split_goal_1 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : (components >= (kv + 1 ))) (PreH2 : (oi < 0)) (PreH3 : (1 <= minimum_pre)) (PreH4 : (minimum_pre <= nv)) (PreH5 : ((-1) <= oi)) (PreH6 : (oi < nv)) (PreH7 : (0 <= components)) (PreH8 : (components <= ((nv - 1 ) - oi ))) (PreH9 : ((Zlength (sizes)) = nv)) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((0 <= (Znth j_2 sizes 0)) /\ ((Znth j_2 sizes 0) <= nv)))) (PreH11 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH12 : (Pre nv kv edges )) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (RootedOrderModel nv edges parent_data order_data )) (PreH15 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < nv)) -> ((((0 <= (Znth j_3 order_data 0)) /\ ((Znth j_3 order_data 0) < nv)) /\ ((-1) <= (Znth j_3 parent_data 0))) /\ ((Znth j_3 parent_data 0) < nv)))) (PreH16 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv sizes )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
.

Definition feasible_return_wit_2_split_goal_2 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : (components >= (kv + 1 ))) (PreH2 : (oi < 0)) (PreH3 : (1 <= minimum_pre)) (PreH4 : (minimum_pre <= nv)) (PreH5 : ((-1) <= oi)) (PreH6 : (oi < nv)) (PreH7 : (0 <= components)) (PreH8 : (components <= ((nv - 1 ) - oi ))) (PreH9 : ((Zlength (sizes)) = nv)) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((0 <= (Znth j_2 sizes 0)) /\ ((Znth j_2 sizes 0) <= nv)))) (PreH11 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH12 : (Pre nv kv edges )) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (RootedOrderModel nv edges parent_data order_data )) (PreH15 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < nv)) -> ((((0 <= (Znth j_3 order_data 0)) /\ ((Znth j_3 order_data 0) < nv)) /\ ((-1) <= (Znth j_3 parent_data 0))) /\ ((Znth j_3 parent_data 0) < nv)))) (PreH16 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv sizes )
|--
  “ ((1 <> 0) <-> (ThresholdFeasible nv kv edges minimum_pre )) ”
.

Definition feasible_return_wit_2_split_goal_spatial :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : (components >= (kv + 1 ))) (PreH2 : (oi < 0)) (PreH3 : (1 <= minimum_pre)) (PreH4 : (minimum_pre <= nv)) (PreH5 : ((-1) <= oi)) (PreH6 : (oi < nv)) (PreH7 : (0 <= components)) (PreH8 : (components <= ((nv - 1 ) - oi ))) (PreH9 : ((Zlength (sizes)) = nv)) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((0 <= (Znth j_2 sizes 0)) /\ ((Znth j_2 sizes 0) <= nv)))) (PreH11 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH12 : (Pre nv kv edges )) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (RootedOrderModel nv edges parent_data order_data )) (PreH15 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < nv)) -> ((((0 <= (Znth j_3 order_data 0)) /\ ((Znth j_3 order_data 0) < nv)) /\ ((-1) <= (Znth j_3 parent_data 0))) /\ ((Znth j_3 parent_data 0) < nv)))) (PreH16 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv sizes )
|--
  (IntArray.undef_full size_p nv )
.

Definition feasible_partial_solve_wit_1 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (i: Z) (initialized: (@list Z)) (PreH1 : (i < nv)) (PreH2 : (1 <= minimum_pre)) (PreH3 : (minimum_pre <= nv)) (PreH4 : (SizeInitializationState nv i initialized )) (PreH5 : (Pre nv kv edges )) (PreH6 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH7 : (RootedOrderModel nv edges parent_data order_data )) (PreH8 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.seg size_p 0 i initialized )
  **  (IntArray.undef_seg size_p i nv )
|--
  “ (i < nv) ”
  &&  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ (SizeInitializationState nv i initialized ) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
  &&  (((size_p + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg size_p (i + 1 ) nv )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.seg size_p 0 i initialized )
.

Definition feasible_partial_solve_wit_2 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : (oi >= 0)) (PreH2 : (1 <= minimum_pre)) (PreH3 : (minimum_pre <= nv)) (PreH4 : ((-1) <= oi)) (PreH5 : (oi < nv)) (PreH6 : (0 <= components)) (PreH7 : (components <= ((nv - 1 ) - oi ))) (PreH8 : ((Zlength (sizes)) = nv)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH10 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH11 : (Pre nv kv edges )) (PreH12 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH13 : (RootedOrderModel nv edges parent_data order_data )) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH15 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.full size_p nv sizes )
|--
  “ (oi >= 0) ”
  &&  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= oi) ”
  &&  “ (oi < nv) ”
  &&  “ (0 <= components) ”
  &&  “ (components <= ((nv - 1 ) - oi )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes ) ”
  &&  (((order_p + (oi * sizeof(INT)))) # Int  |-> (Znth oi order_data 0))
  **  (IntArray.missing_i order_p oi 0 nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full size_p nv sizes )
.

Definition feasible_partial_solve_wit_3 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : (oi >= 0)) (PreH2 : (1 <= minimum_pre)) (PreH3 : (minimum_pre <= nv)) (PreH4 : ((-1) <= oi)) (PreH5 : (oi < nv)) (PreH6 : (0 <= components)) (PreH7 : (components <= ((nv - 1 ) - oi ))) (PreH8 : ((Zlength (sizes)) = nv)) (PreH9 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH10 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH11 : (Pre nv kv edges )) (PreH12 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH13 : (RootedOrderModel nv edges parent_data order_data )) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH15 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full size_p nv sizes )
|--
  “ (oi >= 0) ”
  &&  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= oi) ”
  &&  “ (oi < nv) ”
  &&  “ (0 <= components) ”
  &&  “ (components <= ((nv - 1 ) - oi )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes ) ”
  &&  (((size_p + ((Znth oi order_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth oi order_data 0) sizes 0))
  **  (IntArray.missing_i size_p (Znth oi order_data 0) 0 nv sizes )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
.

Definition feasible_partial_solve_wit_4 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre)) (PreH2 : (oi >= 0)) (PreH3 : (1 <= minimum_pre)) (PreH4 : (minimum_pre <= nv)) (PreH5 : ((-1) <= oi)) (PreH6 : (oi < nv)) (PreH7 : (0 <= components)) (PreH8 : (components <= ((nv - 1 ) - oi ))) (PreH9 : ((Zlength (sizes)) = nv)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH11 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH12 : (Pre nv kv edges )) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (RootedOrderModel nv edges parent_data order_data )) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH16 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv sizes )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
|--
  “ ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre) ”
  &&  “ (oi >= 0) ”
  &&  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= oi) ”
  &&  “ (oi < nv) ”
  &&  “ (0 <= components) ”
  &&  “ (components <= ((nv - 1 ) - oi )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes ) ”
  &&  (((size_p + ((Znth oi order_data 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i size_p (Znth oi order_data 0) 0 nv sizes )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
.

Definition feasible_partial_solve_wit_5 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre)) (PreH2 : (oi >= 0)) (PreH3 : (1 <= minimum_pre)) (PreH4 : (minimum_pre <= nv)) (PreH5 : ((-1) <= oi)) (PreH6 : (oi < nv)) (PreH7 : (0 <= components)) (PreH8 : (components <= ((nv - 1 ) - oi ))) (PreH9 : ((Zlength (sizes)) = nv)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH11 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH12 : (Pre nv kv edges )) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (RootedOrderModel nv edges parent_data order_data )) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH16 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
|--
  “ ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre) ”
  &&  “ (oi >= 0) ”
  &&  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= oi) ”
  &&  “ (oi < nv) ”
  &&  “ (0 <= components) ”
  &&  “ (components <= ((nv - 1 ) - oi )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes ) ”
  &&  (((parent_p + ((Znth oi order_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth oi order_data 0) parent_data 0))
  **  (IntArray.missing_i parent_p (Znth oi order_data 0) 0 nv parent_data )
  **  (IntArray.full size_p nv (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
.

Definition feasible_partial_solve_wit_6 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) sizes 0) < minimum_pre)) (PreH2 : (oi >= 0)) (PreH3 : (1 <= minimum_pre)) (PreH4 : (minimum_pre <= nv)) (PreH5 : ((-1) <= oi)) (PreH6 : (oi < nv)) (PreH7 : (0 <= components)) (PreH8 : (components <= ((nv - 1 ) - oi ))) (PreH9 : ((Zlength (sizes)) = nv)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH11 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH12 : (Pre nv kv edges )) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (RootedOrderModel nv edges parent_data order_data )) (PreH15 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH16 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv sizes )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
|--
  “ ((Znth (Znth oi order_data 0) sizes 0) < minimum_pre) ”
  &&  “ (oi >= 0) ”
  &&  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= oi) ”
  &&  “ (oi < nv) ”
  &&  “ (0 <= components) ”
  &&  “ (components <= ((nv - 1 ) - oi )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes ) ”
  &&  (((parent_p + ((Znth oi order_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth oi order_data 0) parent_data 0))
  **  (IntArray.missing_i parent_p (Znth oi order_data 0) 0 nv parent_data )
  **  (IntArray.full size_p nv sizes )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
.

Definition feasible_partial_solve_wit_7 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full size_p nv (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ ((Znth (Znth oi order_data 0) parent_data 0) >= 0) ”
  &&  “ ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre) ”
  &&  “ (oi >= 0) ”
  &&  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= oi) ”
  &&  “ (oi < nv) ”
  &&  “ (0 <= components) ”
  &&  “ (components <= ((nv - 1 ) - oi )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes ) ”
  &&  (((parent_p + ((Znth oi order_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth oi order_data 0) parent_data 0))
  **  (IntArray.missing_i parent_p (Znth oi order_data 0) 0 nv parent_data )
  **  (IntArray.full size_p nv (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
.

Definition feasible_partial_solve_wit_8 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes 0) < minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full size_p nv sizes )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ ((Znth (Znth oi order_data 0) parent_data 0) >= 0) ”
  &&  “ ((Znth (Znth oi order_data 0) sizes 0) < minimum_pre) ”
  &&  “ (oi >= 0) ”
  &&  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= oi) ”
  &&  “ (oi < nv) ”
  &&  “ (0 <= components) ”
  &&  “ (components <= ((nv - 1 ) - oi )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes ) ”
  &&  (((parent_p + ((Znth oi order_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth oi order_data 0) parent_data 0))
  **  (IntArray.missing_i parent_p (Znth oi order_data 0) 0 nv parent_data )
  **  (IntArray.full size_p nv sizes )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
.

Definition feasible_partial_solve_wit_9 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full size_p nv (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ ((Znth (Znth oi order_data 0) parent_data 0) >= 0) ”
  &&  “ ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre) ”
  &&  “ (oi >= 0) ”
  &&  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= oi) ”
  &&  “ (oi < nv) ”
  &&  “ (0 <= components) ”
  &&  “ (components <= ((nv - 1 ) - oi )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes ) ”
  &&  (((size_p + ((Znth (Znth oi order_data 0) parent_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth (Znth oi order_data 0) parent_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) 0))
  **  (IntArray.missing_i size_p (Znth (Znth oi order_data 0) parent_data 0) 0 nv (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
.

Definition feasible_partial_solve_wit_10 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ ((Znth (Znth oi order_data 0) parent_data 0) >= 0) ”
  &&  “ ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre) ”
  &&  “ (oi >= 0) ”
  &&  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= oi) ”
  &&  “ (oi < nv) ”
  &&  “ (0 <= components) ”
  &&  “ (components <= ((nv - 1 ) - oi )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes ) ”
  &&  (((size_p + ((Znth oi order_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth oi order_data 0) (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) 0))
  **  (IntArray.missing_i size_p (Znth oi order_data 0) 0 nv (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
.

Definition feasible_partial_solve_wit_11 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ ((Znth (Znth oi order_data 0) parent_data 0) >= 0) ”
  &&  “ ((Znth (Znth oi order_data 0) sizes 0) >= minimum_pre) ”
  &&  “ (oi >= 0) ”
  &&  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= oi) ”
  &&  “ (oi < nv) ”
  &&  “ (0 <= components) ”
  &&  “ (components <= ((nv - 1 ) - oi )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes ) ”
  &&  (((size_p + ((Znth (Znth oi order_data 0) parent_data 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i size_p (Znth (Znth oi order_data 0) parent_data 0) 0 nv (replace_Znth ((Znth oi order_data 0)) (0) (sizes)) )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
.

Definition feasible_partial_solve_wit_12 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes 0) < minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full size_p nv sizes )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ ((Znth (Znth oi order_data 0) parent_data 0) >= 0) ”
  &&  “ ((Znth (Znth oi order_data 0) sizes 0) < minimum_pre) ”
  &&  “ (oi >= 0) ”
  &&  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= oi) ”
  &&  “ (oi < nv) ”
  &&  “ (0 <= components) ”
  &&  “ (components <= ((nv - 1 ) - oi )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes ) ”
  &&  (((size_p + ((Znth (Znth oi order_data 0) parent_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0))
  **  (IntArray.missing_i size_p (Znth (Znth oi order_data 0) parent_data 0) 0 nv sizes )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
.

Definition feasible_partial_solve_wit_13 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes 0) < minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv sizes )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ ((Znth (Znth oi order_data 0) parent_data 0) >= 0) ”
  &&  “ ((Znth (Znth oi order_data 0) sizes 0) < minimum_pre) ”
  &&  “ (oi >= 0) ”
  &&  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= oi) ”
  &&  “ (oi < nv) ”
  &&  “ (0 <= components) ”
  &&  “ (components <= ((nv - 1 ) - oi )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes ) ”
  &&  (((size_p + ((Znth oi order_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth oi order_data 0) sizes 0))
  **  (IntArray.missing_i size_p (Znth oi order_data 0) 0 nv sizes )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
.

Definition feasible_partial_solve_wit_14 :=
forall (order_data: (@list Z)) (parent_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (minimum_pre: Z) (sizes: (@list Z)) (components: Z) (oi: Z) (PreH1 : ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) (PreH2 : ((Znth (Znth oi order_data 0) sizes 0) < minimum_pre)) (PreH3 : (oi >= 0)) (PreH4 : (1 <= minimum_pre)) (PreH5 : (minimum_pre <= nv)) (PreH6 : ((-1) <= oi)) (PreH7 : (oi < nv)) (PreH8 : (0 <= components)) (PreH9 : (components <= ((nv - 1 ) - oi ))) (PreH10 : ((Zlength (sizes)) = nv)) (PreH11 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv)))) (PreH12 : (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv))) (PreH13 : (Pre nv kv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (RootedOrderModel nv edges parent_data order_data )) (PreH16 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH17 : (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes )),
  (IntArray.full size_p nv sizes )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ ((Znth (Znth oi order_data 0) parent_data 0) >= 0) ”
  &&  “ ((Znth (Znth oi order_data 0) sizes 0) < minimum_pre) ”
  &&  “ (oi >= 0) ”
  &&  “ (1 <= minimum_pre) ”
  &&  “ (minimum_pre <= nv) ”
  &&  “ ((-1) <= oi) ”
  &&  “ (oi < nv) ”
  &&  “ (0 <= components) ”
  &&  “ (components <= ((nv - 1 ) - oi )) ”
  &&  “ ((Zlength (sizes)) = nv) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((0 <= (Znth j sizes 0)) /\ ((Znth j sizes 0) <= nv))) ”
  &&  “ (((oi >= 0) /\ ((Znth (Znth oi order_data 0) parent_data 0) >= 0)) -> (((Znth (Znth (Znth oi order_data 0) parent_data 0) sizes 0) + (Znth (Znth oi order_data 0) sizes 0) ) <= nv)) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (CutScanState nv kv edges minimum_pre oi components parent_data order_data sizes ) ”
  &&  (((size_p + ((Znth (Znth oi order_data 0) parent_data 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i size_p (Znth (Znth oi order_data 0) parent_data 0) 0 nv sizes )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (next_before: Z) (to_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : ((Zlength (edges)) = (nv - 1 ))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH7 : (Pre nv kv edges )) (PreH8 : (nn_pre = nv)) (PreH9 : (kk_pre = kv)) (PreH10 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH11 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH12 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.undef_full retval nn_pre )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "kk" ) )) # Int  |-> kk_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_before)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ (((2 * nn_pre ) - 2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((2 * nn_pre ) - 2 )) ”
.

Definition solver_safety_wit_2 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (next_before: Z) (to_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : ((Zlength (edges)) = (nv - 1 ))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH7 : (Pre nv kv edges )) (PreH8 : (nn_pre = nv)) (PreH9 : (kk_pre = kv)) (PreH10 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH11 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH12 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.undef_full retval nn_pre )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "kk" ) )) # Int  |-> kk_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_before)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ ((2 * nn_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (2 * nn_pre )) ”
.

Definition solver_safety_wit_3 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (next_before: Z) (to_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : ((Zlength (edges)) = (nv - 1 ))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH7 : (Pre nv kv edges )) (PreH8 : (nn_pre = nv)) (PreH9 : (kk_pre = kv)) (PreH10 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH11 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH12 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.undef_full retval nn_pre )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "kk" ) )) # Int  |-> kk_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_before)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_4 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (next_before: Z) (to_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : ((Zlength (edges)) = (nv - 1 ))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH7 : (Pre nv kv edges )) (PreH8 : (nn_pre = nv)) (PreH9 : (kk_pre = kv)) (PreH10 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH11 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH12 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.undef_full retval nn_pre )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "kk" ) )) # Int  |-> kk_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_before)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_5 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (next_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) (retval_2: Z) __default__Prod_Z_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= kv)) (PreH4 : (kv < nv)) (PreH5 : (nv <= 100000)) (PreH6 : ((Zlength (edges)) = (nv - 1 ))) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH8 : (Pre nv kv edges )) (PreH9 : (nn_pre = nv)) (PreH10 : (kk_pre = kv)) (PreH11 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH12 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH13 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.undef_full retval_2 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval nn_pre )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "kk" ) )) # Int  |-> kk_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> retval_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_before)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ (((2 * nn_pre ) - 2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((2 * nn_pre ) - 2 )) ”
.

Definition solver_safety_wit_6 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (next_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) (retval_2: Z) __default__Prod_Z_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= kv)) (PreH4 : (kv < nv)) (PreH5 : (nv <= 100000)) (PreH6 : ((Zlength (edges)) = (nv - 1 ))) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH8 : (Pre nv kv edges )) (PreH9 : (nn_pre = nv)) (PreH10 : (kk_pre = kv)) (PreH11 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH12 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH13 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.undef_full retval_2 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval nn_pre )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "kk" ) )) # Int  |-> kk_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> retval_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_before)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ ((2 * nn_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (2 * nn_pre )) ”
.

Definition solver_safety_wit_7 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (next_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) (retval_2: Z) __default__Prod_Z_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= kv)) (PreH4 : (kv < nv)) (PreH5 : (nv <= 100000)) (PreH6 : ((Zlength (edges)) = (nv - 1 ))) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH8 : (Pre nv kv edges )) (PreH9 : (nn_pre = nv)) (PreH10 : (kk_pre = kv)) (PreH11 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH12 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH13 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.undef_full retval_2 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval nn_pre )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "kk" ) )) # Int  |-> kk_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> retval_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_before)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_8 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (next_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) (retval_2: Z) __default__Prod_Z_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= kv)) (PreH4 : (kv < nv)) (PreH5 : (nv <= 100000)) (PreH6 : ((Zlength (edges)) = (nv - 1 ))) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH8 : (Pre nv kv edges )) (PreH9 : (nn_pre = nv)) (PreH10 : (kk_pre = kv)) (PreH11 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH12 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH13 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.undef_full retval_2 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval nn_pre )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "kk" ) )) # Int  |-> kk_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> retval_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_before)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_9 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) __default__Prod_Z_Z (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= kv)) (PreH5 : (kv < nv)) (PreH6 : (nv <= 100000)) (PreH7 : ((Zlength (edges)) = (nv - 1 ))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH9 : (Pre nv kv edges )) (PreH10 : (nn_pre = nv)) (PreH11 : (kk_pre = kv)) (PreH12 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH13 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH14 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_3 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval_2 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval nn_pre )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "kk" ) )) # Int  |-> kk_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> retval_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> retval_3)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (head_init: (@list Z)) (i: Z) __default__Prod_Z_Z (PreH1 : (i < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= nv)) (PreH8 : ((Zlength (head_init)) = i)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.seg head_p 0 (i + 1 ) (app (head_init) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg head_p (i + 1 ) nv )
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.undef_full to_p ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p ((2 * nv ) - 2 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_11 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (head_init: (@list Z)) (i: Z) __default__Prod_Z_Z (PreH1 : (i < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= nv)) (PreH8 : ((Zlength (head_init)) = i)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.seg head_p 0 i head_init )
  **  (IntArray.undef_seg head_p i nv )
  **  (IntArray.undef_full to_p ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p ((2 * nv ) - 2 ) )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_12 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (head_init: (@list Z)) (i: Z) __default__Prod_Z_Z (PreH1 : (i < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= nv)) (PreH8 : ((Zlength (head_init)) = i)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.seg head_p 0 i head_init )
  **  (IntArray.undef_seg head_p i nv )
  **  (IntArray.undef_full to_p ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p ((2 * nv ) - 2 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_13 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (head_init: (@list Z)) (i: Z) __default__Prod_Z_Z (PreH1 : (i >= nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= nv)) (PreH8 : ((Zlength (head_init)) = i)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  ((( &( "ec" ) )) # Int  |->_)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.seg head_p 0 i head_init )
  **  (IntArray.undef_seg head_p i nv )
  **  (IntArray.undef_full to_p ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p ((2 * nv ) - 2 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (head_init: (@list Z)) (i: Z) __default__Prod_Z_Z (PreH1 : (i >= nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= nv)) (PreH8 : ((Zlength (head_init)) = i)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "ec" ) )) # Int  |-> 0)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.seg head_p 0 i head_init )
  **  (IntArray.undef_seg head_p i nv )
  **  (IntArray.undef_full to_p ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p ((2 * nv ) - 2 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_15 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (1 <= kv)) (PreH2 : (kv < nv)) (PreH3 : (nv <= 100000)) (PreH4 : (Pre nv kv edges )) (PreH5 : (0 <= i)) (PreH6 : (i <= (nv - 1 ))) (PreH7 : (ec = (2 * i ))) (PreH8 : ((Zlength (head_data)) = nv)) (PreH9 : ((Zlength (to_done)) = ec)) (PreH10 : ((Zlength (next_done)) = ec)) (PreH11 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH12 : (CurrentEdgeFresh edges i )) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 ec to_done )
  **  (IntArray.undef_seg to_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_16 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : (1 <= kv)) (PreH2 : (kv < nv)) (PreH3 : (nv <= 100000)) (PreH4 : (Pre nv kv edges )) (PreH5 : (0 <= i)) (PreH6 : (i <= (nv - 1 ))) (PreH7 : (ec = (2 * i ))) (PreH8 : ((Zlength (head_data)) = nv)) (PreH9 : ((Zlength (to_done)) = ec)) (PreH10 : ((Zlength (next_done)) = ec)) (PreH11 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH12 : (CurrentEdgeFresh edges i )) (PreH13 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 ec to_done )
  **  (IntArray.undef_seg to_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_17 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (to_done)) = ec)) (PreH11 : ((Zlength (next_done)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.full head_p nv (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) )
  **  (IntArray.seg next_p 0 (ec + 1 ) (app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 (ec + 1 ) (app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth i ev_data 0))
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "u" ) )) # Int  |-> (Znth i eu_data 0))
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ ((ec + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (ec + 1 )) ”
.

Definition solver_safety_wit_18 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (to_done)) = ec)) (PreH11 : ((Zlength (next_done)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth i ev_data 0))
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "u" ) )) # Int  |-> (Znth i eu_data 0))
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ec" ) )) # Int  |-> (ec + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ (((ec + 1 ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((ec + 1 ) + 1 )) ”
.

Definition solver_safety_wit_19 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (to_done)) = ec)) (PreH11 : ((Zlength (next_done)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ec" ) )) # Int  |-> ((ec + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_20 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (cells: (@list (@option Z))) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (FreshSizeCells nv cells )) (PreH3 : ((Zlength (cells)) = nv)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= kv)) (PreH8 : (kv < nv)) (PreH9 : (nv <= 100000)) (PreH10 : (Pre nv kv edges )) (PreH11 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH12 : ((Zlength (head_data)) = nv)) (PreH13 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  ((( &( "top" ) )) # Int  |->_)
  **  (IntArray.mixed_full retval_3 nv cells )
  **  (IntArray.undef_full retval_2 nv )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> retval)
  **  ((( &( "order" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> retval_3)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_21 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (cells: (@list (@option Z))) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (FreshSizeCells nv cells )) (PreH3 : ((Zlength (cells)) = nv)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= kv)) (PreH8 : (kv < nv)) (PreH9 : (nv <= 100000)) (PreH10 : (Pre nv kv edges )) (PreH11 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH12 : ((Zlength (head_data)) = nv)) (PreH13 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  ((( &( "top" ) )) # Int  |-> 1)
  **  (IntArray.mixed_full retval_3 nv cells )
  **  (IntArray.undef_full retval_2 nv )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> retval)
  **  ((( &( "order" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> retval_3)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_22 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (cells: (@list (@option Z))) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (FreshSizeCells nv cells )) (PreH3 : ((Zlength (cells)) = nv)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= kv)) (PreH8 : (kv < nv)) (PreH9 : (nv <= 100000)) (PreH10 : (Pre nv kv edges )) (PreH11 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH12 : ((Zlength (head_data)) = nv)) (PreH13 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  ((( &( "top" ) )) # Int  |-> 1)
  **  (IntArray.mixed_full retval_3 nv cells )
  **  (IntArray.undef_full retval_2 nv )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> retval)
  **  ((( &( "order" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> retval_3)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_23 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (cells: (@list (@option Z))) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (FreshSizeCells nv cells )) (PreH3 : ((Zlength (cells)) = nv)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= kv)) (PreH8 : (kv < nv)) (PreH9 : (nv <= 100000)) (PreH10 : (Pre nv kv edges )) (PreH11 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH12 : ((Zlength (head_data)) = nv)) (PreH13 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (((retval_2 + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg retval_2 1 nv )
  **  ((( &( "top" ) )) # Int  |-> 1)
  **  (IntArray.mixed_full retval_3 nv cells )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> retval)
  **  ((( &( "order" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> retval_3)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_24 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (cells: (@list (@option Z))) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (FreshSizeCells nv cells )) (PreH3 : ((Zlength (cells)) = nv)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= kv)) (PreH8 : (kv < nv)) (PreH9 : (nv <= 100000)) (PreH10 : (Pre nv kv edges )) (PreH11 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH12 : ((Zlength (head_data)) = nv)) (PreH13 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (((retval_2 + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg retval_2 1 nv )
  **  ((( &( "top" ) )) # Int  |-> 1)
  **  (IntArray.mixed_full retval_3 nv cells )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> retval)
  **  ((( &( "order" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> retval_3)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_25 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (cells: (@list (@option Z))) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (FreshSizeCells nv cells )) (PreH3 : ((Zlength (cells)) = nv)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= kv)) (PreH8 : (kv < nv)) (PreH9 : (nv <= 100000)) (PreH10 : (Pre nv kv edges )) (PreH11 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH12 : ((Zlength (head_data)) = nv)) (PreH13 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (((retval_2 + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg retval_2 1 nv )
  **  ((( &( "top" ) )) # Int  |-> 1)
  **  (IntArray.mixed_full retval_3 nv cells )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> retval)
  **  ((( &( "order" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> retval_3)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_26 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (cells: (@list (@option Z))) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (FreshSizeCells nv cells )) (PreH3 : ((Zlength (cells)) = nv)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= kv)) (PreH8 : (kv < nv)) (PreH9 : (nv <= 100000)) (PreH10 : (Pre nv kv edges )) (PreH11 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH12 : ((Zlength (head_data)) = nv)) (PreH13 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  ((( &( "i" ) )) # Int  |->_)
  **  (((retval + (0 * sizeof(INT)))) # Int  |-> (-1))
  **  (IntArray.undef_seg retval 1 nv )
  **  (((retval_2 + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg retval_2 1 nv )
  **  ((( &( "top" ) )) # Int  |-> 1)
  **  (IntArray.mixed_full retval_3 nv cells )
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> retval)
  **  ((( &( "order" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> retval_3)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_27 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (e: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i < top)) (PreH4 : (1 <= top)) (PreH5 : (top <= nv)) (PreH6 : (0 <= v)) (PreH7 : (v < nv)) (PreH8 : ((-1) <= parent_v)) (PreH9 : (parent_v < nv)) (PreH10 : (v = (Znth i order_data 0))) (PreH11 : ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v)))) (PreH12 : ((-1) <= e)) (PreH13 : (e < ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (head_data)) = nv)) (PreH15 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH16 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (order_data)) = top)) (PreH18 : ((Zlength (parent_cells)) = nv)) (PreH19 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH20 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH21 : (Pre nv kv edges )) (PreH22 : (TreeAttachmentCut edges )) (PreH23 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH24 : (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e )) (PreH25 : (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv))),
  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "traversal_parent" ) )) # Int  |-> parent_v)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_28 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (e: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i < top)) (PreH4 : (1 <= top)) (PreH5 : (top <= nv)) (PreH6 : (0 <= v)) (PreH7 : (v < nv)) (PreH8 : ((-1) <= parent_v)) (PreH9 : (parent_v < nv)) (PreH10 : (v = (Znth i order_data 0))) (PreH11 : ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v)))) (PreH12 : ((-1) <= e)) (PreH13 : (e < ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (head_data)) = nv)) (PreH15 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH16 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (order_data)) = top)) (PreH18 : ((Zlength (parent_cells)) = nv)) (PreH19 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH20 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH21 : (Pre nv kv edges )) (PreH22 : (TreeAttachmentCut edges )) (PreH23 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH24 : (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e )) (PreH25 : (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv))),
  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "traversal_parent" ) )) # Int  |-> parent_v)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_29 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (e: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (top < nv)) (PreH2 : (e <= INT_MAX)) (PreH3 : (parent_v <= INT_MAX)) (PreH4 : (v <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (ec <= INT_MAX)) (PreH7 : (kv <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (e >= INT_MIN)) (PreH10 : (parent_v >= INT_MIN)) (PreH11 : (v >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (kv >= INT_MIN)) (PreH15 : (nv >= INT_MIN)) (PreH16 : ((Znth e to_data 0) <> parent_v)) (PreH17 : (e <> (-1))) (PreH18 : (ec = ((2 * nv ) - 2 ))) (PreH19 : (0 <= i)) (PreH20 : (i < top)) (PreH21 : (1 <= top)) (PreH22 : (top <= nv)) (PreH23 : (0 <= v)) (PreH24 : (v < nv)) (PreH25 : ((-1) <= parent_v)) (PreH26 : (parent_v < nv)) (PreH27 : (v = (Znth i order_data 0))) (PreH28 : ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v)))) (PreH29 : ((-1) <= e)) (PreH30 : (e < ((2 * nv ) - 2 ))) (PreH31 : ((Zlength (head_data)) = nv)) (PreH32 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH33 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH34 : ((Zlength (order_data)) = top)) (PreH35 : ((Zlength (parent_cells)) = nv)) (PreH36 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH37 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH38 : (Pre nv kv edges )) (PreH39 : (TreeAttachmentCut edges )) (PreH40 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH41 : (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e )) (PreH42 : (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv))),
  (IntArray.seg order_p 0 (top + 1 ) (app (order_data) ((cons ((Znth e to_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg order_p (top + 1 ) nv )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.mixed_full parent_p nv (replace_Znth ((Znth e to_data 0)) ((Some (v))) (parent_cells)) )
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "traversal_parent" ) )) # Int  |-> parent_v)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((top + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (top + 1 )) ”
.

Definition solver_safety_wit_30 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (e: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (e = (-1))) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i < top)) (PreH5 : (1 <= top)) (PreH6 : (top <= nv)) (PreH7 : (0 <= v)) (PreH8 : (v < nv)) (PreH9 : ((-1) <= parent_v)) (PreH10 : (parent_v < nv)) (PreH11 : (v = (Znth i order_data 0))) (PreH12 : ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v)))) (PreH13 : ((-1) <= e)) (PreH14 : (e < ((2 * nv ) - 2 ))) (PreH15 : ((Zlength (head_data)) = nv)) (PreH16 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH18 : ((Zlength (order_data)) = top)) (PreH19 : ((Zlength (parent_cells)) = nv)) (PreH20 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH21 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH22 : (Pre nv kv edges )) (PreH23 : (TreeAttachmentCut edges )) (PreH24 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH25 : (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e )) (PreH26 : (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv))),
  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_31 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (i: Z) (top: Z) (ec: Z) __default__App_option_Z (PreH1 : (i >= top)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= top)) (PreH4 : (top <= nv)) (PreH5 : (0 <= i)) (PreH6 : (i <= top)) (PreH7 : ((Zlength (head_data)) = nv)) (PreH8 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH10 : ((Zlength (order_data)) = top)) (PreH11 : ((Zlength (parent_cells)) = nv)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH14 : (Pre nv kv edges )) (PreH15 : (TreeAttachmentCut edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (TraversalEntryState nv edges i order_data parent_cells )),
  ((( &( "lo" ) )) # Int  |->_)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_32 :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (i: Z) (top: Z) (ec: Z) __default__App_option_Z (PreH1 : (i >= top)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= top)) (PreH4 : (top <= nv)) (PreH5 : (0 <= i)) (PreH6 : (i <= top)) (PreH7 : ((Zlength (head_data)) = nv)) (PreH8 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH10 : ((Zlength (order_data)) = top)) (PreH11 : ((Zlength (parent_cells)) = nv)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH14 : (Pre nv kv edges )) (PreH15 : (TreeAttachmentCut edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (TraversalEntryState nv edges i order_data parent_cells )),
  ((( &( "hi" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> 1)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((nv <> (INT_MIN)) \/ ((kv + 1 ) <> (-1))) ”
  &&  “ ((kv + 1 ) <> 0) ”
) \/
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (i: Z) (top: Z) (ec: Z) __default__App_option_Z (PreH1 : (i >= top)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= top)) (PreH4 : (top <= nv)) (PreH5 : (0 <= i)) (PreH6 : (i <= top)) (PreH7 : ((Zlength (head_data)) = nv)) (PreH8 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH10 : ((Zlength (order_data)) = top)) (PreH11 : ((Zlength (parent_cells)) = nv)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH14 : (Pre nv kv edges )) (PreH15 : (TreeAttachmentCut edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (TraversalEntryState nv edges i order_data parent_cells )),
  ((( &( "hi" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> 1)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((nv <> (INT_MIN)) \/ ((kv + 1 ) <> (-1))) ”
  &&  “ ((kv + 1 ) <> 0) ”
).

Definition solver_safety_wit_32_split_goal_1 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (i: Z) (top: Z) (ec: Z) __default__App_option_Z (PreH1 : (i >= top)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= top)) (PreH4 : (top <= nv)) (PreH5 : (0 <= i)) (PreH6 : (i <= top)) (PreH7 : ((Zlength (head_data)) = nv)) (PreH8 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH10 : ((Zlength (order_data)) = top)) (PreH11 : ((Zlength (parent_cells)) = nv)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH14 : (Pre nv kv edges )) (PreH15 : (TreeAttachmentCut edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (TraversalEntryState nv edges i order_data parent_cells )),
  ((( &( "hi" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> 1)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((nv <> (INT_MIN)) \/ ((kv + 1 ) <> (-1))) ”
.

Definition solver_safety_wit_32_split_goal_2 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (i: Z) (top: Z) (ec: Z) __default__App_option_Z (PreH1 : (i >= top)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= top)) (PreH4 : (top <= nv)) (PreH5 : (0 <= i)) (PreH6 : (i <= top)) (PreH7 : ((Zlength (head_data)) = nv)) (PreH8 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH10 : ((Zlength (order_data)) = top)) (PreH11 : ((Zlength (parent_cells)) = nv)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH14 : (Pre nv kv edges )) (PreH15 : (TreeAttachmentCut edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (TraversalEntryState nv edges i order_data parent_cells )),
  ((( &( "hi" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> 1)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((kv + 1 ) <> 0) ”
.

Definition solver_safety_wit_33 :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (i: Z) (top: Z) (ec: Z) __default__App_option_Z (PreH1 : (i >= top)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= top)) (PreH4 : (top <= nv)) (PreH5 : (0 <= i)) (PreH6 : (i <= top)) (PreH7 : ((Zlength (head_data)) = nv)) (PreH8 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH10 : ((Zlength (order_data)) = top)) (PreH11 : ((Zlength (parent_cells)) = nv)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH14 : (Pre nv kv edges )) (PreH15 : (TreeAttachmentCut edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (TraversalEntryState nv edges i order_data parent_cells )),
  ((( &( "hi" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> 1)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((kv + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (kv + 1 )) ”
) \/
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (i: Z) (top: Z) (ec: Z) __default__App_option_Z (PreH1 : (i >= top)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= top)) (PreH4 : (top <= nv)) (PreH5 : (0 <= i)) (PreH6 : (i <= top)) (PreH7 : ((Zlength (head_data)) = nv)) (PreH8 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH10 : ((Zlength (order_data)) = top)) (PreH11 : ((Zlength (parent_cells)) = nv)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH14 : (Pre nv kv edges )) (PreH15 : (TreeAttachmentCut edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (TraversalEntryState nv edges i order_data parent_cells )),
  ((( &( "hi" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> 1)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((kv + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (kv + 1 )) ”
).

Definition solver_safety_wit_33_split_goal_1 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (i: Z) (top: Z) (ec: Z) __default__App_option_Z (PreH1 : (i >= top)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= top)) (PreH4 : (top <= nv)) (PreH5 : (0 <= i)) (PreH6 : (i <= top)) (PreH7 : ((Zlength (head_data)) = nv)) (PreH8 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH10 : ((Zlength (order_data)) = top)) (PreH11 : ((Zlength (parent_cells)) = nv)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH14 : (Pre nv kv edges )) (PreH15 : (TreeAttachmentCut edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (TraversalEntryState nv edges i order_data parent_cells )),
  ((( &( "hi" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> 1)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((kv + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_33_split_goal_2 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (i: Z) (top: Z) (ec: Z) __default__App_option_Z (PreH1 : (i >= top)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= top)) (PreH4 : (top <= nv)) (PreH5 : (0 <= i)) (PreH6 : (i <= top)) (PreH7 : ((Zlength (head_data)) = nv)) (PreH8 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH10 : ((Zlength (order_data)) = top)) (PreH11 : ((Zlength (parent_cells)) = nv)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH14 : (Pre nv kv edges )) (PreH15 : (TreeAttachmentCut edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (TraversalEntryState nv edges i order_data parent_cells )),
  ((( &( "hi" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> 1)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((INT_MIN) <= (kv + 1 )) ”
.

Definition solver_safety_wit_34 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (i: Z) (top: Z) (ec: Z) __default__App_option_Z (PreH1 : (i >= top)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= top)) (PreH4 : (top <= nv)) (PreH5 : (0 <= i)) (PreH6 : (i <= top)) (PreH7 : ((Zlength (head_data)) = nv)) (PreH8 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH10 : ((Zlength (order_data)) = top)) (PreH11 : ((Zlength (parent_cells)) = nv)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH14 : (Pre nv kv edges )) (PreH15 : (TreeAttachmentCut edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (TraversalEntryState nv edges i order_data parent_cells )),
  ((( &( "hi" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> 1)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_35 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (i: Z) (top: Z) (ec: Z) __default__App_option_Z (PreH1 : (i >= top)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= top)) (PreH4 : (top <= nv)) (PreH5 : (0 <= i)) (PreH6 : (i <= top)) (PreH7 : ((Zlength (head_data)) = nv)) (PreH8 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH10 : ((Zlength (order_data)) = top)) (PreH11 : ((Zlength (parent_cells)) = nv)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH14 : (Pre nv kv edges )) (PreH15 : (TreeAttachmentCut edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (TraversalEntryState nv edges i order_data parent_cells )),
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "hi" ) )) # Int  |-> (nv ÷ (kv + 1 ) ))
  **  ((( &( "lo" ) )) # Int  |-> 1)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_36 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (order_data: (@list Z)) (parent_data: (@list Z)) (head_data: (@list Z)) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (PreH1 : (lo <= hi)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= lo)) (PreH4 : (lo <= (nv + 1 ))) (PreH5 : (0 <= hi)) (PreH6 : (hi <= nv)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))) (PreH15 : (Pre nv kv edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (RootedOrderModel nv edges parent_data order_data )) (PreH18 : (SearchState nv kv edges lo hi ans )),
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (((lo + hi ) <> (INT_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_37 :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (order_data: (@list Z)) (parent_data: (@list Z)) (head_data: (@list Z)) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (PreH1 : (lo <= hi)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= lo)) (PreH4 : (lo <= (nv + 1 ))) (PreH5 : (0 <= hi)) (PreH6 : (hi <= nv)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))) (PreH15 : (Pre nv kv edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (RootedOrderModel nv edges parent_data order_data )) (PreH18 : (SearchState nv kv edges lo hi ans )),
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((lo + hi ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (lo + hi )) ”
) \/
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (order_data: (@list Z)) (parent_data: (@list Z)) (head_data: (@list Z)) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (PreH1 : (lo <= hi)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= lo)) (PreH4 : (lo <= (nv + 1 ))) (PreH5 : (0 <= hi)) (PreH6 : (hi <= nv)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))) (PreH15 : (Pre nv kv edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (RootedOrderModel nv edges parent_data order_data )) (PreH18 : (SearchState nv kv edges lo hi ans )),
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((lo + hi ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (lo + hi )) ”
).

Definition solver_safety_wit_37_split_goal_1 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (order_data: (@list Z)) (parent_data: (@list Z)) (head_data: (@list Z)) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (PreH1 : (lo <= hi)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= lo)) (PreH4 : (lo <= (nv + 1 ))) (PreH5 : (0 <= hi)) (PreH6 : (hi <= nv)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))) (PreH15 : (Pre nv kv edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (RootedOrderModel nv edges parent_data order_data )) (PreH18 : (SearchState nv kv edges lo hi ans )),
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((lo + hi ) <= INT_MAX) ”
.

Definition solver_safety_wit_37_split_goal_2 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (order_data: (@list Z)) (parent_data: (@list Z)) (head_data: (@list Z)) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (PreH1 : (lo <= hi)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= lo)) (PreH4 : (lo <= (nv + 1 ))) (PreH5 : (0 <= hi)) (PreH6 : (hi <= nv)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))) (PreH15 : (Pre nv kv edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (RootedOrderModel nv edges parent_data order_data )) (PreH18 : (SearchState nv kv edges lo hi ans )),
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((INT_MIN) <= (lo + hi )) ”
.

Definition solver_safety_wit_38 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (order_data: (@list Z)) (parent_data: (@list Z)) (head_data: (@list Z)) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (PreH1 : (lo <= hi)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= lo)) (PreH4 : (lo <= (nv + 1 ))) (PreH5 : (0 <= hi)) (PreH6 : (hi <= nv)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))) (PreH15 : (Pre nv kv edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (RootedOrderModel nv edges parent_data order_data )) (PreH18 : (SearchState nv kv edges lo hi ans )),
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_39 :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data)) = nv)) (PreH14 : ((Zlength (parent_data)) = nv)) (PreH15 : ((Zlength (order_data)) = nv)) (PreH16 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH21 : (RootedOrderModel nv edges parent_data order_data )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval <> 0)),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
|--
  “ ((((lo + hi ) ÷ 2 ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((lo + hi ) ÷ 2 ) + 1 )) ”
) \/
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data)) = nv)) (PreH14 : ((Zlength (parent_data)) = nv)) (PreH15 : ((Zlength (order_data)) = nv)) (PreH16 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH21 : (RootedOrderModel nv edges parent_data order_data )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval <> 0)),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
|--
  “ ((((lo + hi ) ÷ 2 ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((lo + hi ) ÷ 2 ) + 1 )) ”
).

Definition solver_safety_wit_39_split_goal_1 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data)) = nv)) (PreH14 : ((Zlength (parent_data)) = nv)) (PreH15 : ((Zlength (order_data)) = nv)) (PreH16 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH21 : (RootedOrderModel nv edges parent_data order_data )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval <> 0)),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
|--
  “ ((((lo + hi ) ÷ 2 ) + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_39_split_goal_2 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data)) = nv)) (PreH14 : ((Zlength (parent_data)) = nv)) (PreH15 : ((Zlength (order_data)) = nv)) (PreH16 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH21 : (RootedOrderModel nv edges parent_data order_data )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval <> 0)),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
|--
  “ ((INT_MIN) <= (((lo + hi ) ÷ 2 ) + 1 )) ”
.

Definition solver_safety_wit_40 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data)) = nv)) (PreH14 : ((Zlength (parent_data)) = nv)) (PreH15 : ((Zlength (order_data)) = nv)) (PreH16 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH21 : (RootedOrderModel nv edges parent_data order_data )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval <> 0)),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_41 :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data)) = nv)) (PreH14 : ((Zlength (parent_data)) = nv)) (PreH15 : ((Zlength (order_data)) = nv)) (PreH16 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH21 : (RootedOrderModel nv edges parent_data order_data )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval = 0)),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
|--
  “ ((((lo + hi ) ÷ 2 ) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((lo + hi ) ÷ 2 ) - 1 )) ”
) \/
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data)) = nv)) (PreH14 : ((Zlength (parent_data)) = nv)) (PreH15 : ((Zlength (order_data)) = nv)) (PreH16 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH21 : (RootedOrderModel nv edges parent_data order_data )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval = 0)),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
|--
  “ ((((lo + hi ) ÷ 2 ) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((lo + hi ) ÷ 2 ) - 1 )) ”
).

Definition solver_safety_wit_41_split_goal_1 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data)) = nv)) (PreH14 : ((Zlength (parent_data)) = nv)) (PreH15 : ((Zlength (order_data)) = nv)) (PreH16 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH21 : (RootedOrderModel nv edges parent_data order_data )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval = 0)),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
|--
  “ ((((lo + hi ) ÷ 2 ) - 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_41_split_goal_2 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data)) = nv)) (PreH14 : ((Zlength (parent_data)) = nv)) (PreH15 : ((Zlength (order_data)) = nv)) (PreH16 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH21 : (RootedOrderModel nv edges parent_data order_data )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval = 0)),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
|--
  “ ((INT_MIN) <= (((lo + hi ) ÷ 2 ) - 1 )) ”
.

Definition solver_safety_wit_42 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data)) = nv)) (PreH14 : ((Zlength (parent_data)) = nv)) (PreH15 : ((Zlength (order_data)) = nv)) (PreH16 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH21 : (RootedOrderModel nv edges parent_data order_data )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval = 0)),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
  **  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 :=
(
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) __default__Prod_Z_Z (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= kv)) (PreH5 : (kv < nv)) (PreH6 : (nv <= 100000)) (PreH7 : ((Zlength (edges)) = (nv - 1 ))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH9 : (Pre nv kv edges )) (PreH10 : (nn_pre = nv)) (PreH11 : (kk_pre = kv)) (PreH12 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH13 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH14 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.undef_full retval_3 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval_2 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval nn_pre )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "kk" ) )) # Int  |-> kk_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> retval_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> retval_3)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  EX (next_p: Z) (to_p: Z) (head_p: Z) (head_init: (@list Z)),
  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= nv) ”
  &&  “ ((Zlength (head_init)) = 0) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < 0)) -> ((Znth q head_init 0) = (-1))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.seg head_p 0 0 head_init )
  **  (IntArray.undef_seg head_p 0 nv )
  **  (IntArray.undef_full to_p ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p ((2 * nv ) - 2 ) )
) \/
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) __default__Prod_Z_Z (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= kv)) (PreH5 : (kv < nv)) (PreH6 : (nv <= 100000)) (PreH7 : ((Zlength (edges)) = (nv - 1 ))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH9 : (Pre nv kv edges )) (PreH10 : (nn_pre = nv)) (PreH11 : (kk_pre = kv)) (PreH12 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH13 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH14 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.undef_full retval_3 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval_2 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval nn_pre )
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < 0)) -> ((Znth q (@nil Z) 0) = (-1))) ”
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.undef_seg retval 0 nv )
  **  (IntArray.undef_full retval_2 ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full retval_3 ((2 * nv ) - 2 ) )
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) __default__Prod_Z_Z (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= kv)) (PreH5 : (kv < nv)) (PreH6 : (nv <= 100000)) (PreH7 : ((Zlength (edges)) = (nv - 1 ))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH9 : (Pre nv kv edges )) (PreH10 : (nn_pre = nv)) (PreH11 : (kk_pre = kv)) (PreH12 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH13 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH14 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.undef_full retval_3 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval_2 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval nn_pre )
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) __default__Prod_Z_Z (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= kv)) (PreH5 : (kv < nv)) (PreH6 : (nv <= 100000)) (PreH7 : ((Zlength (edges)) = (nv - 1 ))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH9 : (Pre nv kv edges )) (PreH10 : (nn_pre = nv)) (PreH11 : (kk_pre = kv)) (PreH12 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH13 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH14 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.undef_full retval_3 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval_2 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval nn_pre )
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
|--
  “ forall (q: Z), (((0 <= q) /\ (q < 0)) -> ((Znth q (@nil Z) 0) = (-1))) ”
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) __default__Prod_Z_Z (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= kv)) (PreH5 : (kv < nv)) (PreH6 : (nv <= 100000)) (PreH7 : ((Zlength (edges)) = (nv - 1 ))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH9 : (Pre nv kv edges )) (PreH10 : (nn_pre = nv)) (PreH11 : (kk_pre = kv)) (PreH12 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH13 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH14 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.undef_full retval_3 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval_2 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval nn_pre )
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
.

Definition solver_entail_wit_1_split_goal_spatial :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) __default__Prod_Z_Z (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= kv)) (PreH5 : (kv < nv)) (PreH6 : (nv <= 100000)) (PreH7 : ((Zlength (edges)) = (nv - 1 ))) (PreH8 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH9 : (Pre nv kv edges )) (PreH10 : (nn_pre = nv)) (PreH11 : (kk_pre = kv)) (PreH12 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH13 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH14 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.undef_full retval_3 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval_2 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval nn_pre )
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
|--
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.undef_seg retval 0 nv )
  **  (IntArray.undef_full retval_2 ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full retval_3 ((2 * nv ) - 2 ) )
.

Definition solver_entail_wit_2 :=
(
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (head_init_2: (@list Z)) (i: Z) __default__Prod_Z_Z (PreH1 : (i < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= nv)) (PreH8 : ((Zlength (head_init_2)) = i)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < i)) -> ((Znth q head_init_2 0) = (-1)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.seg head_p_2 0 (i + 1 ) (app (head_init_2) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg head_p_2 (i + 1 ) nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.undef_full to_p_2 ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p_2 ((2 * nv ) - 2 ) )
|--
  EX (next_p: Z) (to_p: Z) (head_p: Z) (head_init: (@list Z)),
  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= nv) ”
  &&  “ ((Zlength (head_init)) = (i + 1 )) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (i + 1 ))) -> ((Znth q head_init 0) = (-1))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.seg head_p 0 (i + 1 ) head_init )
  **  (IntArray.undef_seg head_p (i + 1 ) nv )
  **  (IntArray.undef_full to_p ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p ((2 * nv ) - 2 ) )
) \/
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_init_2: (@list Z)) (i: Z) __default__Prod_Z_Z (PreH1 : (i < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= nv)) (PreH8 : ((Zlength (head_init_2)) = i)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < i)) -> ((Znth q head_init_2 0) = (-1)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  TT && emp 
|--
  “ ((Zlength ((app (head_init_2) ((cons ((-1)) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_init_2: (@list Z)) (i: Z) __default__Prod_Z_Z (PreH1 : (i < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= nv)) (PreH8 : ((Zlength (head_init_2)) = i)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < i)) -> ((Znth q head_init_2 0) = (-1)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  ((Zlength ((app (head_init_2) ((cons ((-1)) ((@nil Z))))))) = (i + 1 ))
.

Definition solver_entail_wit_3 :=
(
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (head_init: (@list Z)) (i: Z) __default__Prod_Z_Z (PreH1 : (i >= nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= nv)) (PreH8 : ((Zlength (head_init)) = i)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (nv - 1 ))) -> ((((((0 <= (Znth j_2 eu_data 0)) /\ ((Znth j_2 eu_data 0) < nv)) /\ (0 <= (Znth j_2 ev_data 0))) /\ ((Znth j_2 ev_data 0) < nv)) /\ ((Znth j_2 eu_data 0) = ((fst ((Znth j_2 edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j_2 ev_data 0) = ((snd ((Znth j_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.seg head_p_2 0 i head_init )
  **  (IntArray.undef_seg head_p_2 i nv )
  **  (IntArray.undef_full to_p_2 ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p_2 ((2 * nv ) - 2 ) )
|--
  EX (next_p: Z) (to_p: Z) (head_p: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)),
  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (nv - 1 )) ”
  &&  “ (0 = (2 * 0 )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_done)) = 0) ”
  &&  “ ((Zlength (next_done)) = 0) ”
  &&  “ (AdjacencyBuildState nv edges 0 head_data to_done next_done ) ”
  &&  “ (CurrentEdgeFresh edges 0 ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 0 to_done )
  **  (IntArray.undef_seg to_p 0 ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 0 next_done )
  **  (IntArray.undef_seg next_p 0 ((2 * nv ) - 2 ) )
) \/
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_init: (@list Z)) (i: Z) __default__Prod_Z_Z (PreH1 : (i >= nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= nv)) (PreH8 : ((Zlength (head_init)) = i)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (nv - 1 ))) -> ((((((0 <= (Znth j_2 eu_data 0)) /\ ((Znth j_2 eu_data 0) < nv)) /\ (0 <= (Znth j_2 ev_data 0))) /\ ((Znth j_2 ev_data 0) < nv)) /\ ((Znth j_2 eu_data 0) = ((fst ((Znth j_2 edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j_2 ev_data 0) = ((snd ((Znth j_2 edges __default__Prod_Z_Z))) - 1 ))))),
  TT && emp 
|--
  “ forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  “ (CurrentEdgeFresh edges 0 ) ”
  &&  “ (AdjacencyBuildState nv edges 0 head_init (@nil Z) (@nil Z) ) ”
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_init: (@list Z)) (i: Z) __default__Prod_Z_Z (PreH1 : (i >= nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= nv)) (PreH8 : ((Zlength (head_init)) = i)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (nv - 1 ))) -> ((((((0 <= (Znth j_2 eu_data 0)) /\ ((Znth j_2 eu_data 0) < nv)) /\ (0 <= (Znth j_2 ev_data 0))) /\ ((Znth j_2 ev_data 0) < nv)) /\ ((Znth j_2 eu_data 0) = ((fst ((Znth j_2 edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j_2 ev_data 0) = ((snd ((Znth j_2 edges __default__Prod_Z_Z))) - 1 ))))),
  forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_init: (@list Z)) (i: Z) __default__Prod_Z_Z (PreH1 : (i >= nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= nv)) (PreH8 : ((Zlength (head_init)) = i)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (nv - 1 ))) -> ((((((0 <= (Znth j_2 eu_data 0)) /\ ((Znth j_2 eu_data 0) < nv)) /\ (0 <= (Znth j_2 ev_data 0))) /\ ((Znth j_2 ev_data 0) < nv)) /\ ((Znth j_2 eu_data 0) = ((fst ((Znth j_2 edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j_2 ev_data 0) = ((snd ((Znth j_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (CurrentEdgeFresh edges 0 )
.

Definition solver_entail_wit_3_split_goal_3 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_init: (@list Z)) (i: Z) __default__Prod_Z_Z (PreH1 : (i >= nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= nv)) (PreH8 : ((Zlength (head_init)) = i)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (nv - 1 ))) -> ((((((0 <= (Znth j_2 eu_data 0)) /\ ((Znth j_2 eu_data 0) < nv)) /\ (0 <= (Znth j_2 ev_data 0))) /\ ((Znth j_2 ev_data 0) < nv)) /\ ((Znth j_2 eu_data 0) = ((fst ((Znth j_2 edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j_2 ev_data 0) = ((snd ((Znth j_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (AdjacencyBuildState nv edges 0 head_init (@nil Z) (@nil Z) )
.

Definition solver_entail_wit_3_split_goal_4 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_init: (@list Z)) (i: Z) __default__Prod_Z_Z (PreH1 : (i >= nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= nv)) (PreH8 : ((Zlength (head_init)) = i)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (nv - 1 ))) -> ((((((0 <= (Znth j_2 eu_data 0)) /\ ((Znth j_2 eu_data 0) < nv)) /\ (0 <= (Znth j_2 ev_data 0))) /\ ((Znth j_2 ev_data 0) < nv)) /\ ((Znth j_2 eu_data 0) = ((fst ((Znth j_2 edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j_2 ev_data 0) = ((snd ((Znth j_2 edges __default__Prod_Z_Z))) - 1 ))))),
  ((Zlength ((@nil Z))) = 0)
.

Definition solver_entail_wit_3_split_goal_5 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_init: (@list Z)) (i: Z) __default__Prod_Z_Z (PreH1 : (i >= nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= nv)) (PreH8 : ((Zlength (head_init)) = i)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (nv - 1 ))) -> ((((((0 <= (Znth j_2 eu_data 0)) /\ ((Znth j_2 eu_data 0) < nv)) /\ (0 <= (Znth j_2 ev_data 0))) /\ ((Znth j_2 ev_data 0) < nv)) /\ ((Znth j_2 eu_data 0) = ((fst ((Znth j_2 edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j_2 ev_data 0) = ((snd ((Znth j_2 edges __default__Prod_Z_Z))) - 1 ))))),
  ((Zlength ((@nil Z))) = 0)
.

Definition solver_entail_wit_4 :=
(
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (next_done_2: (@list Z)) (to_done_2: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data_2)) = nv)) (PreH10 : ((Zlength (to_done_2)) = ec)) (PreH11 : ((Zlength (next_done_2)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data_2 to_done_2 next_done_2 )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.full head_p_2 nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data_2)))) )
  **  (IntArray.seg next_p_2 0 ((ec + 1 ) + 1 ) (app ((app (next_done_2) ((cons ((Znth (Znth i eu_data 0) head_data_2 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data_2)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p_2 ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p_2 0 ((ec + 1 ) + 1 ) (app ((app (to_done_2) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p_2 ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  EX (next_p: Z) (to_p: Z) (head_p: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)),
  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (nv - 1 )) ”
  &&  “ (((ec + 1 ) + 1 ) = (2 * (i + 1 ) )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_done)) = ((ec + 1 ) + 1 )) ”
  &&  “ ((Zlength (next_done)) = ((ec + 1 ) + 1 )) ”
  &&  “ (AdjacencyBuildState nv edges (i + 1 ) head_data to_done next_done ) ”
  &&  “ (CurrentEdgeFresh edges (i + 1 ) ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) to_done )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) next_done )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
) \/
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (next_done_2: (@list Z)) (to_done_2: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data_2)) = nv)) (PreH10 : ((Zlength (to_done_2)) = ec)) (PreH11 : ((Zlength (next_done_2)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data_2 to_done_2 next_done_2 )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  TT && emp 
|--
  “ (CurrentEdgeFresh edges (i + 1 ) ) ”
  &&  “ (AdjacencyBuildState nv edges (i + 1 ) (replace_Znth ((Znth i ev_data 0)) (((2 * i ) + 1 )) ((replace_Znth ((Znth i eu_data 0)) ((2 * i )) (head_data_2)))) (app ((app (to_done_2) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) (app ((app (next_done_2) ((cons ((Znth (Znth i eu_data 0) head_data_2 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) ((2 * i )) (head_data_2)) 0)) ((@nil Z))))) ) ”
  &&  “ ((Zlength ((app ((app (next_done_2) ((cons ((Znth (Znth i eu_data 0) head_data_2 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) ((2 * i )) (head_data_2)) 0)) ((@nil Z))))))) = (((2 * i ) + 1 ) + 1 )) ”
  &&  “ ((Zlength ((app ((app (to_done_2) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))))) = (((2 * i ) + 1 ) + 1 )) ”
  &&  “ ((Zlength ((replace_Znth ((Znth i ev_data 0)) (((2 * i ) + 1 )) ((replace_Znth ((Znth i eu_data 0)) ((2 * i )) (head_data_2)))))) = nv) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (next_done_2: (@list Z)) (to_done_2: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data_2)) = nv)) (PreH10 : ((Zlength (to_done_2)) = ec)) (PreH11 : ((Zlength (next_done_2)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data_2 to_done_2 next_done_2 )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (CurrentEdgeFresh edges (i + 1 ) )
.

Definition solver_entail_wit_4_split_goal_2 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (next_done_2: (@list Z)) (to_done_2: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data_2)) = nv)) (PreH10 : ((Zlength (to_done_2)) = ec)) (PreH11 : ((Zlength (next_done_2)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data_2 to_done_2 next_done_2 )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (AdjacencyBuildState nv edges (i + 1 ) (replace_Znth ((Znth i ev_data 0)) (((2 * i ) + 1 )) ((replace_Znth ((Znth i eu_data 0)) ((2 * i )) (head_data_2)))) (app ((app (to_done_2) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) (app ((app (next_done_2) ((cons ((Znth (Znth i eu_data 0) head_data_2 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) ((2 * i )) (head_data_2)) 0)) ((@nil Z))))) )
.

Definition solver_entail_wit_4_split_goal_3 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (next_done_2: (@list Z)) (to_done_2: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data_2)) = nv)) (PreH10 : ((Zlength (to_done_2)) = ec)) (PreH11 : ((Zlength (next_done_2)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data_2 to_done_2 next_done_2 )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  ((Zlength ((app ((app (next_done_2) ((cons ((Znth (Znth i eu_data 0) head_data_2 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) ((2 * i )) (head_data_2)) 0)) ((@nil Z))))))) = (((2 * i ) + 1 ) + 1 ))
.

Definition solver_entail_wit_4_split_goal_4 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (next_done_2: (@list Z)) (to_done_2: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data_2)) = nv)) (PreH10 : ((Zlength (to_done_2)) = ec)) (PreH11 : ((Zlength (next_done_2)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data_2 to_done_2 next_done_2 )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  ((Zlength ((app ((app (to_done_2) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))))) = (((2 * i ) + 1 ) + 1 ))
.

Definition solver_entail_wit_4_split_goal_5 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (next_done_2: (@list Z)) (to_done_2: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data_2)) = nv)) (PreH10 : ((Zlength (to_done_2)) = ec)) (PreH11 : ((Zlength (next_done_2)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data_2 to_done_2 next_done_2 )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  ((Zlength ((replace_Znth ((Znth i ev_data 0)) (((2 * i ) + 1 )) ((replace_Znth ((Znth i eu_data 0)) ((2 * i )) (head_data_2)))))) = nv)
.

Definition solver_entail_wit_5 :=
(
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) >= nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data_2)) = nv)) (PreH10 : ((Zlength (to_done)) = ec)) (PreH11 : ((Zlength (next_done)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data_2 to_done next_done )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.seg to_p_2 0 ec to_done )
  **  (IntArray.undef_seg to_p_2 ec ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p_2 0 ec next_done )
  **  (IntArray.undef_seg next_p_2 ec ((2 * nv ) - 2 ) )
|--
  EX (next_p: Z) (to_p: Z) (head_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)),
  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
) \/
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) >= nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data_2)) = nv)) (PreH10 : ((Zlength (to_done)) = ec)) (PreH11 : ((Zlength (next_done)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data_2 to_done next_done )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  TT && emp 
|--
  “ (AdjacencyModel nv edges head_data_2 to_done next_done ) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) >= nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data_2)) = nv)) (PreH10 : ((Zlength (to_done)) = ec)) (PreH11 : ((Zlength (next_done)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data_2 to_done next_done )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (AdjacencyModel nv edges head_data_2 to_done next_done )
.

Definition solver_entail_wit_6 :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p_2: Z) (to_p_2: Z) (next_p_2: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (cells: (@list (@option Z))) (retval_3: Z) (pv: Z) __default__App_option_Z (PreH1 : (retval_3 <> 0)) (PreH2 : (FreshSizeCells nv cells )) (PreH3 : ((Zlength (cells)) = nv)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= kv)) (PreH8 : (kv < nv)) (PreH9 : (nv <= 100000)) (PreH10 : (Pre nv kv edges )) (PreH11 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH12 : ((Zlength (head_data_2)) = nv)) (PreH13 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))),
  (((retval + (0 * sizeof(INT)))) # Int  |-> (-1))
  **  (IntArray.undef_seg retval 1 nv )
  **  (((retval_2 + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg retval_2 1 nv )
  **  (IntArray.mixed_full retval_3 nv cells )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "parent" ) )) # Ptr  |-> retval)
  **  ((( &( "order" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> retval_3)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
|--
  EX (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)),
  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= nv) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 1) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (order_data)) = 1) ”
  &&  “ ((Zlength (parent_cells)) = nv) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < 1)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 )))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (TreeAttachmentCut edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (TraversalEntryState nv edges 0 order_data parent_cells ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 1 order_data )
  **  (IntArray.undef_seg order_p 1 nv )
  **  (IntArray.undef_full size_p nv )
) \/
(
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (cells: (@list (@option Z))) (retval_3: Z) (pv: Z) __default__App_option_Z (PreH1 : (0 <= INT_MAX)) (PreH2 : ((-1) <= INT_MAX)) (PreH3 : (0 >= INT_MIN)) (PreH4 : ((-1) >= INT_MIN)) (PreH5 : (retval_3 <> 0)) (PreH6 : (FreshSizeCells nv cells )) (PreH7 : ((Zlength (cells)) = nv)) (PreH8 : (retval_2 <> 0)) (PreH9 : (retval <> 0)) (PreH10 : (ec = ((2 * nv ) - 2 ))) (PreH11 : (1 <= kv)) (PreH12 : (kv < nv)) (PreH13 : (nv <= 100000)) (PreH14 : (Pre nv kv edges )) (PreH15 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH16 : ((Zlength (head_data_2)) = nv)) (PreH17 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))),
  (((retval + (0 * sizeof(INT)))) # Int  |-> (-1))
  **  (IntArray.undef_seg retval 1 nv )
  **  (((retval_2 + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.mixed_full retval_3 nv cells )
|--
  EX (parent_cells: (@list (@option Z))) (order_data: (@list Z)),
  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= nv) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 1) ”
  &&  “ ((Zlength (head_data_2)) = nv) ”
  &&  “ ((Zlength (to_data_2)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data_2)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (order_data)) = 1) ”
  &&  “ ((Zlength (parent_cells)) = nv) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < 1)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 )))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (TreeAttachmentCut edges ) ”
  &&  “ (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 ) ”
  &&  “ (TraversalEntryState nv edges 0 order_data parent_cells ) ”
  &&  (IntArray.mixed_full retval nv parent_cells )
  **  (IntArray.seg retval_2 0 1 order_data )
  **  (IntArray.undef_full retval_3 nv )
).

Definition solver_entail_wit_7 :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv_2: Z) (size_p_2: Z) (order_p_2: Z) (parent_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (parent_cells_2: (@list (@option Z))) (order_data: (@list Z)) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (i: Z) (top: Z) (ec: Z) (pv: Z) __default__App_option_Z (PreH1 : (i < top)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= top)) (PreH4 : (top <= nv)) (PreH5 : (0 <= i)) (PreH6 : (i <= top)) (PreH7 : ((Zlength (head_data_2)) = nv)) (PreH8 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH10 : ((Zlength (order_data)) = top)) (PreH11 : ((Zlength (parent_cells_2)) = nv)) (PreH12 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < top)) -> (((0 <= (Znth q_3 order_data 0)) /\ ((Znth q_3 order_data 0) < nv)) /\ exists (pv_2: Z), ((((Znth (Znth q_3 order_data 0) parent_cells_2 __default__App_option_Z) = (Some (pv_2))) /\ ((-1) <= pv_2)) /\ (pv_2 < nv))))) (PreH13 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_4 to_data_2 0)) /\ ((Znth q_4 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_4 next_data_2 0))) /\ ((Znth q_4 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH14 : (Pre nv kv edges )) (PreH15 : (TreeAttachmentCut edges )) (PreH16 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH17 : (TraversalEntryState nv edges i order_data parent_cells_2 )),
  (IntArray.seg order_p_2 0 top order_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p_2)
  **  ((( &( "order" ) )) # Ptr  |-> order_p_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.mixed_full parent_p_2 nv parent_cells_2 )
  **  (IntArray.undef_seg order_p_2 top nv )
  **  (IntArray.undef_full size_p_2 nv )
|--
  EX (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (parent_cells: (@list (@option Z))) (parent_v: Z) (order_data_2: (@list Z)),
  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < top) ”
  &&  “ (1 <= top) ”
  &&  “ (top <= nv) ”
  &&  “ (0 <= (Znth (i - 0 ) order_data 0)) ”
  &&  “ ((Znth (i - 0 ) order_data 0) < nv) ”
  &&  “ ((Znth (i - 0 ) order_data 0) = (Znth i order_data_2 0)) ”
  &&  “ ((-1) <= parent_v) ”
  &&  “ (parent_v < nv) ”
  &&  “ ((Znth (Znth (i - 0 ) order_data 0) parent_cells __default__App_option_Z) = (Some (parent_v))) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (order_data_2)) = top) ”
  &&  “ ((Zlength (parent_cells)) = nv) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 )))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (TreeAttachmentCut edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (TraversalEntryState nv edges i order_data_2 parent_cells ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (((parent_p + ((Znth (i - 0 ) order_data 0) * sizeof(INT)))) # Int  |-> parent_v)
  **  (IntArray.mixed_missing_i parent_p (Znth (i - 0 ) order_data 0) 0 nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data_2 )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
) \/
(
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (pv_2: Z) (parent_cells_2: (@list (@option Z))) (order_data: (@list Z)) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (i: Z) (top: Z) (ec: Z) __default__App_option_Z (PreH1 : (i < top)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= top)) (PreH4 : (top <= nv)) (PreH5 : (0 <= i)) (PreH6 : (i <= top)) (PreH7 : ((Zlength (head_data_2)) = nv)) (PreH8 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH10 : ((Zlength (order_data)) = top)) (PreH11 : ((Zlength (parent_cells_2)) = nv)) (PreH12 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < top)) -> (((0 <= (Znth q_3 order_data 0)) /\ ((Znth q_3 order_data 0) < nv)) /\ exists (pv_2: Z), ((((Znth (Znth q_3 order_data 0) parent_cells_2 __default__App_option_Z) = (Some (pv_2))) /\ ((-1) <= pv_2)) /\ (pv_2 < nv))))) (PreH13 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_4 to_data_2 0)) /\ ((Znth q_4 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_4 next_data_2 0))) /\ ((Znth q_4 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH14 : (Pre nv kv edges )) (PreH15 : (TreeAttachmentCut edges )) (PreH16 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH17 : (TraversalEntryState nv edges i order_data parent_cells_2 )),
  TT && emp 
|--
  EX (v1: Z),
  “ ((Znth (Znth (i - 0 ) order_data 0) parent_cells_2 __default__App_option_Z) = (Some (v1))) ”
  &&  “ (0 <= (Znth (i - 0 ) order_data 0)) ”
  &&  “ ((Znth (i - 0 ) order_data 0) < (Zlength (head_data_2))) ”
  &&  “ ((Znth (i - 0 ) order_data 0) = (Znth i order_data 0)) ”
  &&  “ ((-1) <= v1) ”
  &&  “ (v1 < (Zlength (head_data_2))) ”
  &&  “ ((Znth (Znth (i - 0 ) order_data 0) parent_cells_2 __default__App_option_Z) = (Some (v1))) ”
  &&  emp
).

Definition solver_entail_wit_8 :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p_2: Z) (to_p_2: Z) (next_p_2: Z) (parent_p_2: Z) (order_p_2: Z) (size_p_2: Z) (head_data: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (order_data_2: (@list Z)) (parent_cells_2: (@list (@option Z))) (parent_v: Z) (pv_2: Z) (ec: Z) (i: Z) (top: Z) (v: Z) (pv: Z) __default__App_option_Z (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i < top)) (PreH4 : (1 <= top)) (PreH5 : (top <= nv)) (PreH6 : (0 <= v)) (PreH7 : (v < nv)) (PreH8 : (v = (Znth i order_data_2 0))) (PreH9 : ((-1) <= parent_v)) (PreH10 : (parent_v < nv)) (PreH11 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH12 : ((Zlength (head_data)) = nv)) (PreH13 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH15 : ((Zlength (order_data_2)) = top)) (PreH16 : ((Zlength (parent_cells_2)) = nv)) (PreH17 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < top)) -> (((0 <= (Znth q_3 order_data_2 0)) /\ ((Znth q_3 order_data_2 0) < nv)) /\ exists (pv_2: Z), ((((Znth (Znth q_3 order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv_2))) /\ ((-1) <= pv_2)) /\ (pv_2 < nv))))) (PreH18 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_4 to_data_2 0)) /\ ((Znth q_4 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_4 next_data_2 0))) /\ ((Znth q_4 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH19 : (Pre nv kv edges )) (PreH20 : (TreeAttachmentCut edges )) (PreH21 : (AdjacencyModel nv edges head_data to_data_2 next_data_2 )) (PreH22 : (TraversalEntryState nv edges i order_data_2 parent_cells_2 )),
  (IntArray.mixed_full parent_p_2 nv parent_cells_2 )
  **  (IntArray.full head_p_2 nv head_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p_2)
  **  ((( &( "order" ) )) # Ptr  |-> order_p_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p_2)
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.seg order_p_2 0 top order_data_2 )
  **  (IntArray.undef_seg order_p_2 top nv )
  **  (IntArray.undef_full size_p_2 nv )
|--
  EX (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (head_data_2: (@list Z)) (parent_cells: (@list (@option Z))) (order_data: (@list Z)),
  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < top) ”
  &&  “ (1 <= top) ”
  &&  “ (top <= nv) ”
  &&  “ (0 <= v) ”
  &&  “ (v < nv) ”
  &&  “ ((-1) <= parent_v) ”
  &&  “ (parent_v < nv) ”
  &&  “ (v = (Znth i order_data 0)) ”
  &&  “ ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v))) ”
  &&  “ ((-1) <= (Znth v head_data 0)) ”
  &&  “ ((Znth v head_data 0) < ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (head_data_2)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (order_data)) = top) ”
  &&  “ ((Zlength (parent_cells)) = nv) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 )))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (TreeAttachmentCut edges ) ”
  &&  “ (AdjacencyModel nv edges head_data_2 to_data next_data ) ”
  &&  “ (TraversalAdjState nv edges i order_data parent_cells head_data_2 to_data next_data v parent_v (Znth v head_data 0) ) ”
  &&  “ ((((Znth v head_data 0) <> (-1)) /\ ((Znth (Znth v head_data 0) to_data 0) <> parent_v)) -> (top < nv)) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data_2 )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
) \/
(
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_data: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (order_data_2: (@list Z)) (parent_cells_2: (@list (@option Z))) (parent_v: Z) (pv_2: Z) (ec: Z) (i: Z) (top: Z) (v: Z) (pv: Z) __default__App_option_Z (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i < top)) (PreH4 : (1 <= top)) (PreH5 : (top <= nv)) (PreH6 : (0 <= v)) (PreH7 : (v < nv)) (PreH8 : (v = (Znth i order_data_2 0))) (PreH9 : ((-1) <= parent_v)) (PreH10 : (parent_v < nv)) (PreH11 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH12 : ((Zlength (head_data)) = nv)) (PreH13 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH15 : ((Zlength (order_data_2)) = top)) (PreH16 : ((Zlength (parent_cells_2)) = nv)) (PreH17 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < top)) -> (((0 <= (Znth q_3 order_data_2 0)) /\ ((Znth q_3 order_data_2 0) < nv)) /\ exists (pv_2: Z), ((((Znth (Znth q_3 order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv_2))) /\ ((-1) <= pv_2)) /\ (pv_2 < nv))))) (PreH18 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_4 to_data_2 0)) /\ ((Znth q_4 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_4 next_data_2 0))) /\ ((Znth q_4 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH19 : (Pre nv kv edges )) (PreH20 : (TreeAttachmentCut edges )) (PreH21 : (AdjacencyModel nv edges head_data to_data_2 next_data_2 )) (PreH22 : (TraversalEntryState nv edges i order_data_2 parent_cells_2 )),
  TT && emp 
|--
  “ ((((Znth v head_data 0) <> (-1)) /\ ((Znth (Znth v head_data 0) to_data_2 0) <> parent_v)) -> (top < nv)) ”
  &&  “ (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data to_data_2 next_data_2 v parent_v (Znth v head_data 0) ) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  “ ((Znth v head_data 0) < ((2 * nv ) - 2 )) ”
  &&  “ ((-1) <= (Znth v head_data 0)) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_data: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (order_data_2: (@list Z)) (parent_cells_2: (@list (@option Z))) (parent_v: Z) (pv_2: Z) (ec: Z) (i: Z) (top: Z) (v: Z) __default__App_option_Z (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i < top)) (PreH4 : (1 <= top)) (PreH5 : (top <= nv)) (PreH6 : (0 <= v)) (PreH7 : (v < nv)) (PreH8 : (v = (Znth i order_data_2 0))) (PreH9 : ((-1) <= parent_v)) (PreH10 : (parent_v < nv)) (PreH11 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH12 : ((Zlength (head_data)) = nv)) (PreH13 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH15 : ((Zlength (order_data_2)) = top)) (PreH16 : ((Zlength (parent_cells_2)) = nv)) (PreH17 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < top)) -> (((0 <= (Znth q_3 order_data_2 0)) /\ ((Znth q_3 order_data_2 0) < nv)) /\ exists (pv_2: Z), ((((Znth (Znth q_3 order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv_2))) /\ ((-1) <= pv_2)) /\ (pv_2 < nv))))) (PreH18 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_4 to_data_2 0)) /\ ((Znth q_4 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_4 next_data_2 0))) /\ ((Znth q_4 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH19 : (Pre nv kv edges )) (PreH20 : (TreeAttachmentCut edges )) (PreH21 : (AdjacencyModel nv edges head_data to_data_2 next_data_2 )) (PreH22 : (TraversalEntryState nv edges i order_data_2 parent_cells_2 )),
  ((((Znth v head_data 0) <> (-1)) /\ ((Znth (Znth v head_data 0) to_data_2 0) <> parent_v)) -> (top < nv))
.

Definition solver_entail_wit_8_split_goal_2 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_data: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (order_data_2: (@list Z)) (parent_cells_2: (@list (@option Z))) (parent_v: Z) (pv_2: Z) (ec: Z) (i: Z) (top: Z) (v: Z) __default__App_option_Z (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i < top)) (PreH4 : (1 <= top)) (PreH5 : (top <= nv)) (PreH6 : (0 <= v)) (PreH7 : (v < nv)) (PreH8 : (v = (Znth i order_data_2 0))) (PreH9 : ((-1) <= parent_v)) (PreH10 : (parent_v < nv)) (PreH11 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH12 : ((Zlength (head_data)) = nv)) (PreH13 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH15 : ((Zlength (order_data_2)) = top)) (PreH16 : ((Zlength (parent_cells_2)) = nv)) (PreH17 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < top)) -> (((0 <= (Znth q_3 order_data_2 0)) /\ ((Znth q_3 order_data_2 0) < nv)) /\ exists (pv_2: Z), ((((Znth (Znth q_3 order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv_2))) /\ ((-1) <= pv_2)) /\ (pv_2 < nv))))) (PreH18 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_4 to_data_2 0)) /\ ((Znth q_4 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_4 next_data_2 0))) /\ ((Znth q_4 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH19 : (Pre nv kv edges )) (PreH20 : (TreeAttachmentCut edges )) (PreH21 : (AdjacencyModel nv edges head_data to_data_2 next_data_2 )) (PreH22 : (TraversalEntryState nv edges i order_data_2 parent_cells_2 )),
  (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data to_data_2 next_data_2 v parent_v (Znth v head_data 0) )
.

Definition solver_entail_wit_8_split_goal_3 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_data: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (order_data_2: (@list Z)) (parent_cells_2: (@list (@option Z))) (parent_v: Z) (pv_2: Z) (ec: Z) (i: Z) (top: Z) (v: Z) __default__App_option_Z (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i < top)) (PreH4 : (1 <= top)) (PreH5 : (top <= nv)) (PreH6 : (0 <= v)) (PreH7 : (v < nv)) (PreH8 : (v = (Znth i order_data_2 0))) (PreH9 : ((-1) <= parent_v)) (PreH10 : (parent_v < nv)) (PreH11 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH12 : ((Zlength (head_data)) = nv)) (PreH13 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH15 : ((Zlength (order_data_2)) = top)) (PreH16 : ((Zlength (parent_cells_2)) = nv)) (PreH17 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < top)) -> (((0 <= (Znth q_3 order_data_2 0)) /\ ((Znth q_3 order_data_2 0) < nv)) /\ exists (pv_2: Z), ((((Znth (Znth q_3 order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv_2))) /\ ((-1) <= pv_2)) /\ (pv_2 < nv))))) (PreH18 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_4 to_data_2 0)) /\ ((Znth q_4 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_4 next_data_2 0))) /\ ((Znth q_4 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH19 : (Pre nv kv edges )) (PreH20 : (TreeAttachmentCut edges )) (PreH21 : (AdjacencyModel nv edges head_data to_data_2 next_data_2 )) (PreH22 : (TraversalEntryState nv edges i order_data_2 parent_cells_2 )),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 ))))
.

Definition solver_entail_wit_8_split_goal_4 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_data: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (order_data_2: (@list Z)) (parent_cells_2: (@list (@option Z))) (parent_v: Z) (pv_2: Z) (ec: Z) (i: Z) (top: Z) (v: Z) (pv: Z) __default__App_option_Z (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i < top)) (PreH4 : (1 <= top)) (PreH5 : (top <= nv)) (PreH6 : (0 <= v)) (PreH7 : (v < nv)) (PreH8 : (v = (Znth i order_data_2 0))) (PreH9 : ((-1) <= parent_v)) (PreH10 : (parent_v < nv)) (PreH11 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH12 : ((Zlength (head_data)) = nv)) (PreH13 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH15 : ((Zlength (order_data_2)) = top)) (PreH16 : ((Zlength (parent_cells_2)) = nv)) (PreH17 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < top)) -> (((0 <= (Znth q_3 order_data_2 0)) /\ ((Znth q_3 order_data_2 0) < nv)) /\ exists (pv_2: Z), ((((Znth (Znth q_3 order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv_2))) /\ ((-1) <= pv_2)) /\ (pv_2 < nv))))) (PreH18 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_4 to_data_2 0)) /\ ((Znth q_4 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_4 next_data_2 0))) /\ ((Znth q_4 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH19 : (Pre nv kv edges )) (PreH20 : (TreeAttachmentCut edges )) (PreH21 : (AdjacencyModel nv edges head_data to_data_2 next_data_2 )) (PreH22 : (TraversalEntryState nv edges i order_data_2 parent_cells_2 )),
  forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))
.

Definition solver_entail_wit_8_split_goal_5 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_data: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (order_data_2: (@list Z)) (parent_cells_2: (@list (@option Z))) (parent_v: Z) (pv_2: Z) (ec: Z) (i: Z) (top: Z) (v: Z) __default__App_option_Z (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i < top)) (PreH4 : (1 <= top)) (PreH5 : (top <= nv)) (PreH6 : (0 <= v)) (PreH7 : (v < nv)) (PreH8 : (v = (Znth i order_data_2 0))) (PreH9 : ((-1) <= parent_v)) (PreH10 : (parent_v < nv)) (PreH11 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH12 : ((Zlength (head_data)) = nv)) (PreH13 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH15 : ((Zlength (order_data_2)) = top)) (PreH16 : ((Zlength (parent_cells_2)) = nv)) (PreH17 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < top)) -> (((0 <= (Znth q_3 order_data_2 0)) /\ ((Znth q_3 order_data_2 0) < nv)) /\ exists (pv_2: Z), ((((Znth (Znth q_3 order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv_2))) /\ ((-1) <= pv_2)) /\ (pv_2 < nv))))) (PreH18 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_4 to_data_2 0)) /\ ((Znth q_4 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_4 next_data_2 0))) /\ ((Znth q_4 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH19 : (Pre nv kv edges )) (PreH20 : (TreeAttachmentCut edges )) (PreH21 : (AdjacencyModel nv edges head_data to_data_2 next_data_2 )) (PreH22 : (TraversalEntryState nv edges i order_data_2 parent_cells_2 )),
  ((Znth v head_data 0) < ((2 * nv ) - 2 ))
.

Definition solver_entail_wit_8_split_goal_6 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_data: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (order_data_2: (@list Z)) (parent_cells_2: (@list (@option Z))) (parent_v: Z) (pv_2: Z) (ec: Z) (i: Z) (top: Z) (v: Z) __default__App_option_Z (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i < top)) (PreH4 : (1 <= top)) (PreH5 : (top <= nv)) (PreH6 : (0 <= v)) (PreH7 : (v < nv)) (PreH8 : (v = (Znth i order_data_2 0))) (PreH9 : ((-1) <= parent_v)) (PreH10 : (parent_v < nv)) (PreH11 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH12 : ((Zlength (head_data)) = nv)) (PreH13 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH15 : ((Zlength (order_data_2)) = top)) (PreH16 : ((Zlength (parent_cells_2)) = nv)) (PreH17 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < top)) -> (((0 <= (Znth q_3 order_data_2 0)) /\ ((Znth q_3 order_data_2 0) < nv)) /\ exists (pv_2: Z), ((((Znth (Znth q_3 order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv_2))) /\ ((-1) <= pv_2)) /\ (pv_2 < nv))))) (PreH18 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_4 to_data_2 0)) /\ ((Znth q_4 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_4 next_data_2 0))) /\ ((Znth q_4 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH19 : (Pre nv kv edges )) (PreH20 : (TreeAttachmentCut edges )) (PreH21 : (AdjacencyModel nv edges head_data to_data_2 next_data_2 )) (PreH22 : (TraversalEntryState nv edges i order_data_2 parent_cells_2 )),
  ((-1) <= (Znth v head_data 0))
.

Definition solver_entail_wit_9 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (e: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : ((Znth e to_data 0) <> parent_v)) (PreH2 : (e <> (-1))) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (0 <= i)) (PreH5 : (i < top)) (PreH6 : (1 <= top)) (PreH7 : (top <= nv)) (PreH8 : (0 <= v)) (PreH9 : (v < nv)) (PreH10 : ((-1) <= parent_v)) (PreH11 : (parent_v < nv)) (PreH12 : (v = (Znth i order_data 0))) (PreH13 : ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v)))) (PreH14 : ((-1) <= e)) (PreH15 : (e < ((2 * nv ) - 2 ))) (PreH16 : ((Zlength (head_data)) = nv)) (PreH17 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH18 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH19 : ((Zlength (order_data)) = top)) (PreH20 : ((Zlength (parent_cells)) = nv)) (PreH21 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH22 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH23 : (Pre nv kv edges )) (PreH24 : (TreeAttachmentCut edges )) (PreH25 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH26 : (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e )) (PreH27 : (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv))),
  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "traversal_parent" ) )) # Int  |-> parent_v)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ (top < nv) ”
  &&  “ (e <= INT_MAX) ”
  &&  “ (parent_v <= INT_MAX) ”
  &&  “ (v <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (ec <= INT_MAX) ”
  &&  “ (kv <= INT_MAX) ”
  &&  “ (nv <= INT_MAX) ”
  &&  “ (e >= INT_MIN) ”
  &&  “ (parent_v >= INT_MIN) ”
  &&  “ (v >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (ec >= INT_MIN) ”
  &&  “ (kv >= INT_MIN) ”
  &&  “ (nv >= INT_MIN) ”
  &&  “ ((Znth e to_data 0) <> parent_v) ”
  &&  “ (e <> (-1)) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < top) ”
  &&  “ (1 <= top) ”
  &&  “ (top <= nv) ”
  &&  “ (0 <= v) ”
  &&  “ (v < nv) ”
  &&  “ ((-1) <= parent_v) ”
  &&  “ (parent_v < nv) ”
  &&  “ (v = (Znth i order_data 0)) ”
  &&  “ ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v))) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (order_data)) = top) ”
  &&  “ ((Zlength (parent_cells)) = nv) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 )))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (TreeAttachmentCut edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e ) ”
  &&  “ (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv)) ”
  &&  ((( &( "top" ) )) # Int  |-> top)
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "traversal_parent" ) )) # Int  |-> parent_v)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
.

Definition solver_entail_wit_10 :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (pv_2: Z) (size_p_2: Z) (order_p_2: Z) (parent_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (e: Z) (parent_cells_2: (@list (@option Z))) (order_data_2: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (e = (-1))) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i < top)) (PreH5 : (1 <= top)) (PreH6 : (top <= nv)) (PreH7 : (0 <= v)) (PreH8 : (v < nv)) (PreH9 : ((-1) <= parent_v)) (PreH10 : (parent_v < nv)) (PreH11 : (v = (Znth i order_data_2 0))) (PreH12 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH13 : ((-1) <= e)) (PreH14 : (e < ((2 * nv ) - 2 ))) (PreH15 : ((Zlength (head_data_2)) = nv)) (PreH16 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : ((Zlength (order_data_2)) = top)) (PreH19 : ((Zlength (parent_cells_2)) = nv)) (PreH20 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < top)) -> (((0 <= (Znth q_3 order_data_2 0)) /\ ((Znth q_3 order_data_2 0) < nv)) /\ exists (pv_2: Z), ((((Znth (Znth q_3 order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv_2))) /\ ((-1) <= pv_2)) /\ (pv_2 < nv))))) (PreH21 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_4 to_data_2 0)) /\ ((Znth q_4 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_4 next_data_2 0))) /\ ((Znth q_4 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH22 : (Pre nv kv edges )) (PreH23 : (TreeAttachmentCut edges )) (PreH24 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH25 : (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v e )) (PreH26 : (((e <> (-1)) /\ ((Znth e to_data_2 0) <> parent_v)) -> (top < nv))),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p_2)
  **  ((( &( "order" ) )) # Ptr  |-> order_p_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.mixed_full parent_p_2 nv parent_cells_2 )
  **  (IntArray.seg order_p_2 0 top order_data_2 )
  **  (IntArray.undef_seg order_p_2 top nv )
  **  (IntArray.undef_full size_p_2 nv )
|--
  EX (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)),
  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= top) ”
  &&  “ (top <= nv) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= top) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (order_data)) = top) ”
  &&  “ ((Zlength (parent_cells)) = nv) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 )))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (TreeAttachmentCut edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (TraversalEntryState nv edges (i + 1 ) order_data parent_cells ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
) \/
(
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (pv: Z) (pv_2: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (e: Z) (parent_cells_2: (@list (@option Z))) (order_data_2: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (e = (-1))) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i < top)) (PreH5 : (1 <= top)) (PreH6 : (top <= nv)) (PreH7 : (0 <= v)) (PreH8 : (v < nv)) (PreH9 : ((-1) <= parent_v)) (PreH10 : (parent_v < nv)) (PreH11 : (v = (Znth i order_data_2 0))) (PreH12 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH13 : ((-1) <= e)) (PreH14 : (e < ((2 * nv ) - 2 ))) (PreH15 : ((Zlength (head_data_2)) = nv)) (PreH16 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : ((Zlength (order_data_2)) = top)) (PreH19 : ((Zlength (parent_cells_2)) = nv)) (PreH20 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < top)) -> (((0 <= (Znth q_3 order_data_2 0)) /\ ((Znth q_3 order_data_2 0) < nv)) /\ exists (pv_2: Z), ((((Znth (Znth q_3 order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv_2))) /\ ((-1) <= pv_2)) /\ (pv_2 < nv))))) (PreH21 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_4 to_data_2 0)) /\ ((Znth q_4 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_4 next_data_2 0))) /\ ((Znth q_4 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH22 : (Pre nv kv edges )) (PreH23 : (TreeAttachmentCut edges )) (PreH24 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH25 : (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v e )) (PreH26 : (((e <> (-1)) /\ ((Znth e to_data_2 0) <> parent_v)) -> (top < nv))),
  TT && emp 
|--
  “ (TraversalEntryState nv edges (i + 1 ) order_data_2 parent_cells_2 ) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  emp
).

Definition solver_entail_wit_10_split_goal_1 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (pv_2: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (e: Z) (parent_cells_2: (@list (@option Z))) (order_data_2: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (e = (-1))) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i < top)) (PreH5 : (1 <= top)) (PreH6 : (top <= nv)) (PreH7 : (0 <= v)) (PreH8 : (v < nv)) (PreH9 : ((-1) <= parent_v)) (PreH10 : (parent_v < nv)) (PreH11 : (v = (Znth i order_data_2 0))) (PreH12 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH13 : ((-1) <= e)) (PreH14 : (e < ((2 * nv ) - 2 ))) (PreH15 : ((Zlength (head_data_2)) = nv)) (PreH16 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : ((Zlength (order_data_2)) = top)) (PreH19 : ((Zlength (parent_cells_2)) = nv)) (PreH20 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < top)) -> (((0 <= (Znth q_3 order_data_2 0)) /\ ((Znth q_3 order_data_2 0) < nv)) /\ exists (pv_2: Z), ((((Znth (Znth q_3 order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv_2))) /\ ((-1) <= pv_2)) /\ (pv_2 < nv))))) (PreH21 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_4 to_data_2 0)) /\ ((Znth q_4 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_4 next_data_2 0))) /\ ((Znth q_4 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH22 : (Pre nv kv edges )) (PreH23 : (TreeAttachmentCut edges )) (PreH24 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH25 : (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v e )) (PreH26 : (((e <> (-1)) /\ ((Znth e to_data_2 0) <> parent_v)) -> (top < nv))),
  (TraversalEntryState nv edges (i + 1 ) order_data_2 parent_cells_2 )
.

Definition solver_entail_wit_10_split_goal_2 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (pv_2: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (e: Z) (parent_cells_2: (@list (@option Z))) (order_data_2: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (e = (-1))) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i < top)) (PreH5 : (1 <= top)) (PreH6 : (top <= nv)) (PreH7 : (0 <= v)) (PreH8 : (v < nv)) (PreH9 : ((-1) <= parent_v)) (PreH10 : (parent_v < nv)) (PreH11 : (v = (Znth i order_data_2 0))) (PreH12 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH13 : ((-1) <= e)) (PreH14 : (e < ((2 * nv ) - 2 ))) (PreH15 : ((Zlength (head_data_2)) = nv)) (PreH16 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : ((Zlength (order_data_2)) = top)) (PreH19 : ((Zlength (parent_cells_2)) = nv)) (PreH20 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < top)) -> (((0 <= (Znth q_3 order_data_2 0)) /\ ((Znth q_3 order_data_2 0) < nv)) /\ exists (pv_2: Z), ((((Znth (Znth q_3 order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv_2))) /\ ((-1) <= pv_2)) /\ (pv_2 < nv))))) (PreH21 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_4 to_data_2 0)) /\ ((Znth q_4 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_4 next_data_2 0))) /\ ((Znth q_4 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH22 : (Pre nv kv edges )) (PreH23 : (TreeAttachmentCut edges )) (PreH24 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH25 : (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v e )) (PreH26 : (((e <> (-1)) /\ ((Znth e to_data_2 0) <> parent_v)) -> (top < nv))),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 ))))
.

Definition solver_entail_wit_10_split_goal_3 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (pv: Z) (pv_2: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (e: Z) (parent_cells_2: (@list (@option Z))) (order_data_2: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (e = (-1))) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i < top)) (PreH5 : (1 <= top)) (PreH6 : (top <= nv)) (PreH7 : (0 <= v)) (PreH8 : (v < nv)) (PreH9 : ((-1) <= parent_v)) (PreH10 : (parent_v < nv)) (PreH11 : (v = (Znth i order_data_2 0))) (PreH12 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH13 : ((-1) <= e)) (PreH14 : (e < ((2 * nv ) - 2 ))) (PreH15 : ((Zlength (head_data_2)) = nv)) (PreH16 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : ((Zlength (order_data_2)) = top)) (PreH19 : ((Zlength (parent_cells_2)) = nv)) (PreH20 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < top)) -> (((0 <= (Znth q_3 order_data_2 0)) /\ ((Znth q_3 order_data_2 0) < nv)) /\ exists (pv_2: Z), ((((Znth (Znth q_3 order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv_2))) /\ ((-1) <= pv_2)) /\ (pv_2 < nv))))) (PreH21 : forall (q_4: Z), (((0 <= q_4) /\ (q_4 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_4 to_data_2 0)) /\ ((Znth q_4 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_4 next_data_2 0))) /\ ((Znth q_4 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH22 : (Pre nv kv edges )) (PreH23 : (TreeAttachmentCut edges )) (PreH24 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH25 : (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v e )) (PreH26 : (((e <> (-1)) /\ ((Znth e to_data_2 0) <> parent_v)) -> (top < nv))),
  forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))
.

Definition solver_entail_wit_11_1 :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p_2: Z) (order_p_2: Z) (parent_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (e: Z) (parent_cells_2: (@list (@option Z))) (order_data_2: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (top < nv)) (PreH2 : (e <= INT_MAX)) (PreH3 : (parent_v <= INT_MAX)) (PreH4 : (v <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (ec <= INT_MAX)) (PreH7 : (kv <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (e >= INT_MIN)) (PreH10 : (parent_v >= INT_MIN)) (PreH11 : (v >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (kv >= INT_MIN)) (PreH15 : (nv >= INT_MIN)) (PreH16 : ((Znth e to_data_2 0) <> parent_v)) (PreH17 : (e <> (-1))) (PreH18 : (ec = ((2 * nv ) - 2 ))) (PreH19 : (0 <= i)) (PreH20 : (i < top)) (PreH21 : (1 <= top)) (PreH22 : (top <= nv)) (PreH23 : (0 <= v)) (PreH24 : (v < nv)) (PreH25 : ((-1) <= parent_v)) (PreH26 : (parent_v < nv)) (PreH27 : (v = (Znth i order_data_2 0))) (PreH28 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH29 : ((-1) <= e)) (PreH30 : (e < ((2 * nv ) - 2 ))) (PreH31 : ((Zlength (head_data_2)) = nv)) (PreH32 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH33 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH34 : ((Zlength (order_data_2)) = top)) (PreH35 : ((Zlength (parent_cells_2)) = nv)) (PreH36 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH37 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH38 : (Pre nv kv edges )) (PreH39 : (TreeAttachmentCut edges )) (PreH40 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH41 : (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v e )) (PreH42 : (((e <> (-1)) /\ ((Znth e to_data_2 0) <> parent_v)) -> (top < nv))),
  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.seg order_p_2 0 (top + 1 ) (app (order_data_2) ((cons ((Znth e to_data_2 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg order_p_2 (top + 1 ) nv )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.mixed_full parent_p_2 nv (replace_Znth ((Znth e to_data_2 0)) ((Some (v))) (parent_cells_2)) )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p_2)
  **  ((( &( "order" ) )) # Ptr  |-> order_p_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.undef_full size_p_2 nv )
|--
  EX (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (parent_cells: (@list (@option Z))) (order_data: (@list Z)),
  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (top + 1 )) ”
  &&  “ (1 <= (top + 1 )) ”
  &&  “ ((top + 1 ) <= nv) ”
  &&  “ (0 <= v) ”
  &&  “ (v < nv) ”
  &&  “ ((-1) <= parent_v) ”
  &&  “ (parent_v < nv) ”
  &&  “ (v = (Znth i order_data 0)) ”
  &&  “ ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v))) ”
  &&  “ ((-1) <= (Znth e next_data_2 0)) ”
  &&  “ ((Znth e next_data_2 0) < ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (order_data)) = (top + 1 )) ”
  &&  “ ((Zlength (parent_cells)) = nv) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (top + 1 ))) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 )))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (TreeAttachmentCut edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v (Znth e next_data_2 0) ) ”
  &&  “ ((((Znth e next_data_2 0) <> (-1)) /\ ((Znth (Znth e next_data_2 0) to_data 0) <> parent_v)) -> ((top + 1 ) < nv)) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 (top + 1 ) order_data )
  **  (IntArray.undef_seg order_p (top + 1 ) nv )
  **  (IntArray.undef_full size_p nv )
) \/
(
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (pv: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (e: Z) (parent_cells_2: (@list (@option Z))) (order_data_2: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (top < nv)) (PreH2 : (e <= INT_MAX)) (PreH3 : (parent_v <= INT_MAX)) (PreH4 : (v <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (ec <= INT_MAX)) (PreH7 : (kv <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (e >= INT_MIN)) (PreH10 : (parent_v >= INT_MIN)) (PreH11 : (v >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (kv >= INT_MIN)) (PreH15 : (nv >= INT_MIN)) (PreH16 : ((Znth e to_data_2 0) <> parent_v)) (PreH17 : (e <> (-1))) (PreH18 : (ec = ((2 * nv ) - 2 ))) (PreH19 : (0 <= i)) (PreH20 : (i < top)) (PreH21 : (1 <= top)) (PreH22 : (top <= nv)) (PreH23 : (0 <= v)) (PreH24 : (v < nv)) (PreH25 : ((-1) <= parent_v)) (PreH26 : (parent_v < nv)) (PreH27 : (v = (Znth i order_data_2 0))) (PreH28 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH29 : ((-1) <= e)) (PreH30 : (e < ((2 * nv ) - 2 ))) (PreH31 : ((Zlength (head_data_2)) = nv)) (PreH32 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH33 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH34 : ((Zlength (order_data_2)) = top)) (PreH35 : ((Zlength (parent_cells_2)) = nv)) (PreH36 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH37 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH38 : (Pre nv kv edges )) (PreH39 : (TreeAttachmentCut edges )) (PreH40 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH41 : (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v e )) (PreH42 : (((e <> (-1)) /\ ((Znth e to_data_2 0) <> parent_v)) -> (top < nv))),
  TT && emp 
|--
  “ ((((Znth e next_data_2 0) <> (-1)) /\ ((Znth (Znth e next_data_2 0) to_data_2 0) <> parent_v)) -> ((top + 1 ) < nv)) ”
  &&  “ (TraversalAdjState nv edges i (app (order_data_2) ((cons ((Znth e to_data_2 0)) ((@nil Z))))) (replace_Znth ((Znth e to_data_2 0)) ((Some (v))) (parent_cells_2)) head_data_2 to_data_2 next_data_2 v parent_v (Znth e next_data_2 0) ) ”
  &&  “ ((Zlength ((replace_Znth ((Znth e to_data_2 0)) ((Some (v))) (parent_cells_2)))) = nv) ”
  &&  “ ((Zlength ((app (order_data_2) ((cons ((Znth e to_data_2 0)) ((@nil Z))))))) = (top + 1 )) ”
  &&  “ ((Znth v (replace_Znth ((Znth e to_data_2 0)) ((Some (v))) (parent_cells_2)) __default__App_option_Z) = (Some (parent_v))) ”
  &&  “ (v = (Znth i (app (order_data_2) ((cons ((Znth e to_data_2 0)) ((@nil Z))))) 0)) ”
  &&  emp
).

Definition solver_entail_wit_11_1_split_goal_1 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (pv: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (e: Z) (parent_cells_2: (@list (@option Z))) (order_data_2: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (top < nv)) (PreH2 : (e <= INT_MAX)) (PreH3 : (parent_v <= INT_MAX)) (PreH4 : (v <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (ec <= INT_MAX)) (PreH7 : (kv <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (e >= INT_MIN)) (PreH10 : (parent_v >= INT_MIN)) (PreH11 : (v >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (kv >= INT_MIN)) (PreH15 : (nv >= INT_MIN)) (PreH16 : ((Znth e to_data_2 0) <> parent_v)) (PreH17 : (e <> (-1))) (PreH18 : (ec = ((2 * nv ) - 2 ))) (PreH19 : (0 <= i)) (PreH20 : (i < top)) (PreH21 : (1 <= top)) (PreH22 : (top <= nv)) (PreH23 : (0 <= v)) (PreH24 : (v < nv)) (PreH25 : ((-1) <= parent_v)) (PreH26 : (parent_v < nv)) (PreH27 : (v = (Znth i order_data_2 0))) (PreH28 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH29 : ((-1) <= e)) (PreH30 : (e < ((2 * nv ) - 2 ))) (PreH31 : ((Zlength (head_data_2)) = nv)) (PreH32 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH33 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH34 : ((Zlength (order_data_2)) = top)) (PreH35 : ((Zlength (parent_cells_2)) = nv)) (PreH36 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH37 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH38 : (Pre nv kv edges )) (PreH39 : (TreeAttachmentCut edges )) (PreH40 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH41 : (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v e )) (PreH42 : (((e <> (-1)) /\ ((Znth e to_data_2 0) <> parent_v)) -> (top < nv))),
  ((((Znth e next_data_2 0) <> (-1)) /\ ((Znth (Znth e next_data_2 0) to_data_2 0) <> parent_v)) -> ((top + 1 ) < nv))
.

Definition solver_entail_wit_11_1_split_goal_2 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (pv: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (e: Z) (parent_cells_2: (@list (@option Z))) (order_data_2: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (top < nv)) (PreH2 : (e <= INT_MAX)) (PreH3 : (parent_v <= INT_MAX)) (PreH4 : (v <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (ec <= INT_MAX)) (PreH7 : (kv <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (e >= INT_MIN)) (PreH10 : (parent_v >= INT_MIN)) (PreH11 : (v >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (kv >= INT_MIN)) (PreH15 : (nv >= INT_MIN)) (PreH16 : ((Znth e to_data_2 0) <> parent_v)) (PreH17 : (e <> (-1))) (PreH18 : (ec = ((2 * nv ) - 2 ))) (PreH19 : (0 <= i)) (PreH20 : (i < top)) (PreH21 : (1 <= top)) (PreH22 : (top <= nv)) (PreH23 : (0 <= v)) (PreH24 : (v < nv)) (PreH25 : ((-1) <= parent_v)) (PreH26 : (parent_v < nv)) (PreH27 : (v = (Znth i order_data_2 0))) (PreH28 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH29 : ((-1) <= e)) (PreH30 : (e < ((2 * nv ) - 2 ))) (PreH31 : ((Zlength (head_data_2)) = nv)) (PreH32 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH33 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH34 : ((Zlength (order_data_2)) = top)) (PreH35 : ((Zlength (parent_cells_2)) = nv)) (PreH36 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH37 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH38 : (Pre nv kv edges )) (PreH39 : (TreeAttachmentCut edges )) (PreH40 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH41 : (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v e )) (PreH42 : (((e <> (-1)) /\ ((Znth e to_data_2 0) <> parent_v)) -> (top < nv))),
  (TraversalAdjState nv edges i (app (order_data_2) ((cons ((Znth e to_data_2 0)) ((@nil Z))))) (replace_Znth ((Znth e to_data_2 0)) ((Some (v))) (parent_cells_2)) head_data_2 to_data_2 next_data_2 v parent_v (Znth e next_data_2 0) )
.

Definition solver_entail_wit_11_1_split_goal_3 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (pv: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (e: Z) (parent_cells_2: (@list (@option Z))) (order_data_2: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (top < nv)) (PreH2 : (e <= INT_MAX)) (PreH3 : (parent_v <= INT_MAX)) (PreH4 : (v <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (ec <= INT_MAX)) (PreH7 : (kv <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (e >= INT_MIN)) (PreH10 : (parent_v >= INT_MIN)) (PreH11 : (v >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (kv >= INT_MIN)) (PreH15 : (nv >= INT_MIN)) (PreH16 : ((Znth e to_data_2 0) <> parent_v)) (PreH17 : (e <> (-1))) (PreH18 : (ec = ((2 * nv ) - 2 ))) (PreH19 : (0 <= i)) (PreH20 : (i < top)) (PreH21 : (1 <= top)) (PreH22 : (top <= nv)) (PreH23 : (0 <= v)) (PreH24 : (v < nv)) (PreH25 : ((-1) <= parent_v)) (PreH26 : (parent_v < nv)) (PreH27 : (v = (Znth i order_data_2 0))) (PreH28 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH29 : ((-1) <= e)) (PreH30 : (e < ((2 * nv ) - 2 ))) (PreH31 : ((Zlength (head_data_2)) = nv)) (PreH32 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH33 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH34 : ((Zlength (order_data_2)) = top)) (PreH35 : ((Zlength (parent_cells_2)) = nv)) (PreH36 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH37 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH38 : (Pre nv kv edges )) (PreH39 : (TreeAttachmentCut edges )) (PreH40 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH41 : (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v e )) (PreH42 : (((e <> (-1)) /\ ((Znth e to_data_2 0) <> parent_v)) -> (top < nv))),
  ((Zlength ((replace_Znth ((Znth e to_data_2 0)) ((Some (v))) (parent_cells_2)))) = nv)
.

Definition solver_entail_wit_11_1_split_goal_4 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (pv: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (e: Z) (parent_cells_2: (@list (@option Z))) (order_data_2: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (top < nv)) (PreH2 : (e <= INT_MAX)) (PreH3 : (parent_v <= INT_MAX)) (PreH4 : (v <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (ec <= INT_MAX)) (PreH7 : (kv <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (e >= INT_MIN)) (PreH10 : (parent_v >= INT_MIN)) (PreH11 : (v >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (kv >= INT_MIN)) (PreH15 : (nv >= INT_MIN)) (PreH16 : ((Znth e to_data_2 0) <> parent_v)) (PreH17 : (e <> (-1))) (PreH18 : (ec = ((2 * nv ) - 2 ))) (PreH19 : (0 <= i)) (PreH20 : (i < top)) (PreH21 : (1 <= top)) (PreH22 : (top <= nv)) (PreH23 : (0 <= v)) (PreH24 : (v < nv)) (PreH25 : ((-1) <= parent_v)) (PreH26 : (parent_v < nv)) (PreH27 : (v = (Znth i order_data_2 0))) (PreH28 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH29 : ((-1) <= e)) (PreH30 : (e < ((2 * nv ) - 2 ))) (PreH31 : ((Zlength (head_data_2)) = nv)) (PreH32 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH33 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH34 : ((Zlength (order_data_2)) = top)) (PreH35 : ((Zlength (parent_cells_2)) = nv)) (PreH36 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH37 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH38 : (Pre nv kv edges )) (PreH39 : (TreeAttachmentCut edges )) (PreH40 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH41 : (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v e )) (PreH42 : (((e <> (-1)) /\ ((Znth e to_data_2 0) <> parent_v)) -> (top < nv))),
  ((Zlength ((app (order_data_2) ((cons ((Znth e to_data_2 0)) ((@nil Z))))))) = (top + 1 ))
.

Definition solver_entail_wit_11_1_split_goal_5 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (pv: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (e: Z) (parent_cells_2: (@list (@option Z))) (order_data_2: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (top < nv)) (PreH2 : (e <= INT_MAX)) (PreH3 : (parent_v <= INT_MAX)) (PreH4 : (v <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (ec <= INT_MAX)) (PreH7 : (kv <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (e >= INT_MIN)) (PreH10 : (parent_v >= INT_MIN)) (PreH11 : (v >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (kv >= INT_MIN)) (PreH15 : (nv >= INT_MIN)) (PreH16 : ((Znth e to_data_2 0) <> parent_v)) (PreH17 : (e <> (-1))) (PreH18 : (ec = ((2 * nv ) - 2 ))) (PreH19 : (0 <= i)) (PreH20 : (i < top)) (PreH21 : (1 <= top)) (PreH22 : (top <= nv)) (PreH23 : (0 <= v)) (PreH24 : (v < nv)) (PreH25 : ((-1) <= parent_v)) (PreH26 : (parent_v < nv)) (PreH27 : (v = (Znth i order_data_2 0))) (PreH28 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH29 : ((-1) <= e)) (PreH30 : (e < ((2 * nv ) - 2 ))) (PreH31 : ((Zlength (head_data_2)) = nv)) (PreH32 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH33 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH34 : ((Zlength (order_data_2)) = top)) (PreH35 : ((Zlength (parent_cells_2)) = nv)) (PreH36 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH37 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH38 : (Pre nv kv edges )) (PreH39 : (TreeAttachmentCut edges )) (PreH40 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH41 : (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v e )) (PreH42 : (((e <> (-1)) /\ ((Znth e to_data_2 0) <> parent_v)) -> (top < nv))),
  ((Znth v (replace_Znth ((Znth e to_data_2 0)) ((Some (v))) (parent_cells_2)) __default__App_option_Z) = (Some (parent_v)))
.

Definition solver_entail_wit_11_1_split_goal_6 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (pv: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (e: Z) (parent_cells_2: (@list (@option Z))) (order_data_2: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (top < nv)) (PreH2 : (e <= INT_MAX)) (PreH3 : (parent_v <= INT_MAX)) (PreH4 : (v <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (ec <= INT_MAX)) (PreH7 : (kv <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (e >= INT_MIN)) (PreH10 : (parent_v >= INT_MIN)) (PreH11 : (v >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (kv >= INT_MIN)) (PreH15 : (nv >= INT_MIN)) (PreH16 : ((Znth e to_data_2 0) <> parent_v)) (PreH17 : (e <> (-1))) (PreH18 : (ec = ((2 * nv ) - 2 ))) (PreH19 : (0 <= i)) (PreH20 : (i < top)) (PreH21 : (1 <= top)) (PreH22 : (top <= nv)) (PreH23 : (0 <= v)) (PreH24 : (v < nv)) (PreH25 : ((-1) <= parent_v)) (PreH26 : (parent_v < nv)) (PreH27 : (v = (Znth i order_data_2 0))) (PreH28 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH29 : ((-1) <= e)) (PreH30 : (e < ((2 * nv ) - 2 ))) (PreH31 : ((Zlength (head_data_2)) = nv)) (PreH32 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH33 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH34 : ((Zlength (order_data_2)) = top)) (PreH35 : ((Zlength (parent_cells_2)) = nv)) (PreH36 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH37 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH38 : (Pre nv kv edges )) (PreH39 : (TreeAttachmentCut edges )) (PreH40 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH41 : (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v e )) (PreH42 : (((e <> (-1)) /\ ((Znth e to_data_2 0) <> parent_v)) -> (top < nv))),
  (v = (Znth i (app (order_data_2) ((cons ((Znth e to_data_2 0)) ((@nil Z))))) 0))
.

Definition solver_entail_wit_11_2 :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p_2: Z) (order_p_2: Z) (parent_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (e: Z) (parent_cells_2: (@list (@option Z))) (order_data_2: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : ((Znth e to_data_2 0) = parent_v)) (PreH2 : (e <> (-1))) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (0 <= i)) (PreH5 : (i < top)) (PreH6 : (1 <= top)) (PreH7 : (top <= nv)) (PreH8 : (0 <= v)) (PreH9 : (v < nv)) (PreH10 : ((-1) <= parent_v)) (PreH11 : (parent_v < nv)) (PreH12 : (v = (Znth i order_data_2 0))) (PreH13 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH14 : ((-1) <= e)) (PreH15 : (e < ((2 * nv ) - 2 ))) (PreH16 : ((Zlength (head_data_2)) = nv)) (PreH17 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH19 : ((Zlength (order_data_2)) = top)) (PreH20 : ((Zlength (parent_cells_2)) = nv)) (PreH21 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH22 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH23 : (Pre nv kv edges )) (PreH24 : (TreeAttachmentCut edges )) (PreH25 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH26 : (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v e )) (PreH27 : (((e <> (-1)) /\ ((Znth e to_data_2 0) <> parent_v)) -> (top < nv))),
  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p_2)
  **  ((( &( "order" ) )) # Ptr  |-> order_p_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.mixed_full parent_p_2 nv parent_cells_2 )
  **  (IntArray.seg order_p_2 0 top order_data_2 )
  **  (IntArray.undef_seg order_p_2 top nv )
  **  (IntArray.undef_full size_p_2 nv )
|--
  EX (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (parent_cells: (@list (@option Z))) (order_data: (@list Z)),
  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < top) ”
  &&  “ (1 <= top) ”
  &&  “ (top <= nv) ”
  &&  “ (0 <= v) ”
  &&  “ (v < nv) ”
  &&  “ ((-1) <= parent_v) ”
  &&  “ (parent_v < nv) ”
  &&  “ (v = (Znth i order_data 0)) ”
  &&  “ ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v))) ”
  &&  “ ((-1) <= (Znth e next_data_2 0)) ”
  &&  “ ((Znth e next_data_2 0) < ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (order_data)) = top) ”
  &&  “ ((Zlength (parent_cells)) = nv) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 )))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (TreeAttachmentCut edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v (Znth e next_data_2 0) ) ”
  &&  “ ((((Znth e next_data_2 0) <> (-1)) /\ ((Znth (Znth e next_data_2 0) to_data 0) <> parent_v)) -> (top < nv)) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
) \/
(
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (pv: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (e: Z) (parent_cells_2: (@list (@option Z))) (order_data_2: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : ((Znth e to_data_2 0) = parent_v)) (PreH2 : (e <> (-1))) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (0 <= i)) (PreH5 : (i < top)) (PreH6 : (1 <= top)) (PreH7 : (top <= nv)) (PreH8 : (0 <= v)) (PreH9 : (v < nv)) (PreH10 : ((-1) <= parent_v)) (PreH11 : (parent_v < nv)) (PreH12 : (v = (Znth i order_data_2 0))) (PreH13 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH14 : ((-1) <= e)) (PreH15 : (e < ((2 * nv ) - 2 ))) (PreH16 : ((Zlength (head_data_2)) = nv)) (PreH17 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH19 : ((Zlength (order_data_2)) = top)) (PreH20 : ((Zlength (parent_cells_2)) = nv)) (PreH21 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH22 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH23 : (Pre nv kv edges )) (PreH24 : (TreeAttachmentCut edges )) (PreH25 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH26 : (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v e )) (PreH27 : (((e <> (-1)) /\ ((Znth e to_data_2 0) <> parent_v)) -> (top < nv))),
  TT && emp 
|--
  “ ((((Znth e next_data_2 0) <> (-1)) /\ ((Znth (Znth e next_data_2 0) to_data_2 0) <> parent_v)) -> (top < nv)) ”
  &&  “ (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v (Znth e next_data_2 0) ) ”
  &&  emp
).

Definition solver_entail_wit_11_2_split_goal_1 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (pv: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (e: Z) (parent_cells_2: (@list (@option Z))) (order_data_2: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : ((Znth e to_data_2 0) = parent_v)) (PreH2 : (e <> (-1))) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (0 <= i)) (PreH5 : (i < top)) (PreH6 : (1 <= top)) (PreH7 : (top <= nv)) (PreH8 : (0 <= v)) (PreH9 : (v < nv)) (PreH10 : ((-1) <= parent_v)) (PreH11 : (parent_v < nv)) (PreH12 : (v = (Znth i order_data_2 0))) (PreH13 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH14 : ((-1) <= e)) (PreH15 : (e < ((2 * nv ) - 2 ))) (PreH16 : ((Zlength (head_data_2)) = nv)) (PreH17 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH19 : ((Zlength (order_data_2)) = top)) (PreH20 : ((Zlength (parent_cells_2)) = nv)) (PreH21 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH22 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH23 : (Pre nv kv edges )) (PreH24 : (TreeAttachmentCut edges )) (PreH25 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH26 : (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v e )) (PreH27 : (((e <> (-1)) /\ ((Znth e to_data_2 0) <> parent_v)) -> (top < nv))),
  ((((Znth e next_data_2 0) <> (-1)) /\ ((Znth (Znth e next_data_2 0) to_data_2 0) <> parent_v)) -> (top < nv))
.

Definition solver_entail_wit_11_2_split_goal_2 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (pv: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (e: Z) (parent_cells_2: (@list (@option Z))) (order_data_2: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : ((Znth e to_data_2 0) = parent_v)) (PreH2 : (e <> (-1))) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (0 <= i)) (PreH5 : (i < top)) (PreH6 : (1 <= top)) (PreH7 : (top <= nv)) (PreH8 : (0 <= v)) (PreH9 : (v < nv)) (PreH10 : ((-1) <= parent_v)) (PreH11 : (parent_v < nv)) (PreH12 : (v = (Znth i order_data_2 0))) (PreH13 : ((Znth v parent_cells_2 __default__App_option_Z) = (Some (parent_v)))) (PreH14 : ((-1) <= e)) (PreH15 : (e < ((2 * nv ) - 2 ))) (PreH16 : ((Zlength (head_data_2)) = nv)) (PreH17 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH19 : ((Zlength (order_data_2)) = top)) (PreH20 : ((Zlength (parent_cells_2)) = nv)) (PreH21 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells_2 __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH22 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH23 : (Pre nv kv edges )) (PreH24 : (TreeAttachmentCut edges )) (PreH25 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH26 : (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v e )) (PreH27 : (((e <> (-1)) /\ ((Znth e to_data_2 0) <> parent_v)) -> (top < nv))),
  (TraversalAdjState nv edges i order_data_2 parent_cells_2 head_data_2 to_data_2 next_data_2 v parent_v (Znth e next_data_2 0) )
.

Definition solver_entail_wit_12 :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p_2: Z) (order_p_2: Z) (parent_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (parent_cells: (@list (@option Z))) (order_data_2: (@list Z)) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (i: Z) (top: Z) (ec: Z) __default__App_option_Z (PreH1 : (i >= top)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= top)) (PreH4 : (top <= nv)) (PreH5 : (0 <= i)) (PreH6 : (i <= top)) (PreH7 : ((Zlength (head_data_2)) = nv)) (PreH8 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH10 : ((Zlength (order_data_2)) = top)) (PreH11 : ((Zlength (parent_cells)) = nv)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH14 : (Pre nv kv edges )) (PreH15 : (TreeAttachmentCut edges )) (PreH16 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH17 : (TraversalEntryState nv edges i order_data_2 parent_cells )),
  ((( &( "top" ) )) # Int  |-> top)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p_2)
  **  ((( &( "order" ) )) # Ptr  |-> order_p_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.mixed_full parent_p_2 nv parent_cells )
  **  (IntArray.seg order_p_2 0 top order_data_2 )
  **  (IntArray.undef_seg order_p_2 top nv )
  **  (IntArray.undef_full size_p_2 nv )
|--
  EX (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (order_data: (@list Z)) (parent_data: (@list Z)) (head_data: (@list Z)),
  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (parent_data)) = nv) ”
  &&  “ ((Zlength (order_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ (SearchState nv kv edges 1 (nv ÷ (kv + 1 ) ) 1 ) ”
  &&  ((( &( "top" ) )) # Int  |-> nv)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
) \/
(
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (pv: Z) (order_p_2: Z) (parent_p_2: Z) (parent_cells: (@list (@option Z))) (order_data_2: (@list Z)) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (head_data_2: (@list Z)) (i: Z) (top: Z) (ec: Z) __default__App_option_Z (PreH1 : (i >= top)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= top)) (PreH4 : (top <= nv)) (PreH5 : (0 <= i)) (PreH6 : (i <= top)) (PreH7 : ((Zlength (head_data_2)) = nv)) (PreH8 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH10 : ((Zlength (order_data_2)) = top)) (PreH11 : ((Zlength (parent_cells)) = nv)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data_2 0)) /\ ((Znth q order_data_2 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data_2 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data_2 0)) /\ ((Znth q_2 to_data_2 0) < nv)) /\ ((-1) <= (Znth q_2 next_data_2 0))) /\ ((Znth q_2 next_data_2 0) < ((2 * nv ) - 2 ))))) (PreH14 : (Pre nv kv edges )) (PreH15 : (TreeAttachmentCut edges )) (PreH16 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH17 : (TraversalEntryState nv edges i order_data_2 parent_cells )),
  (IntArray.mixed_full parent_p_2 nv parent_cells )
  **  (IntArray.seg order_p_2 0 top order_data_2 )
  **  (IntArray.undef_seg order_p_2 top nv )
|--
  EX (order_data: (@list Z)) (parent_data: (@list Z)),
  “ (top = nv) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ ((Zlength (head_data_2)) = nv) ”
  &&  “ ((Zlength (parent_data)) = nv) ”
  &&  “ ((Zlength (order_data)) = nv) ”
  &&  “ ((Zlength (to_data_2)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data_2)) = ((2 * nv ) - 2 )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ (SearchState nv kv edges 1 (nv ÷ (kv + 1 ) ) 1 ) ”
  &&  (IntArray.full parent_p_2 nv parent_data )
  **  (IntArray.full order_p_2 nv order_data )
).

Definition solver_entail_wit_13 :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p_2: Z) (to_p_2: Z) (next_p_2: Z) (parent_p_2: Z) (order_p_2: Z) (size_p_2: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (ec: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : ((Zlength (head_data_2)) = nv)) (PreH6 : ((Zlength (parent_data_2)) = nv)) (PreH7 : ((Zlength (order_data_2)) = nv)) (PreH8 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH11 : (Pre nv kv edges )) (PreH12 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH13 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH14 : (SearchState nv kv edges lo hi ans )),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p_2)
  **  ((( &( "order" ) )) # Ptr  |-> order_p_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full parent_p_2 nv parent_data_2 )
  **  (IntArray.full order_p_2 nv order_data_2 )
  **  (IntArray.undef_full size_p_2 nv )
|--
  EX (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (order_data: (@list Z)) (parent_data: (@list Z)) (head_data: (@list Z)),
  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= lo) ”
  &&  “ (lo <= (nv + 1 )) ”
  &&  “ (0 <= hi) ”
  &&  “ (hi <= nv) ”
  &&  “ (1 <= ans) ”
  &&  “ (ans <= nv) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (parent_data)) = nv) ”
  &&  “ ((Zlength (order_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ (SearchState nv kv edges lo hi ans ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
) \/
(
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (ec: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : ((Zlength (head_data_2)) = nv)) (PreH6 : ((Zlength (parent_data_2)) = nv)) (PreH7 : ((Zlength (order_data_2)) = nv)) (PreH8 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH11 : (Pre nv kv edges )) (PreH12 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH13 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH14 : (SearchState nv kv edges lo hi ans )),
  TT && emp 
|--
  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data_2 0)) /\ ((Znth j order_data_2 0) < nv)) /\ ((-1) <= (Znth j parent_data_2 0))) /\ ((Znth j parent_data_2 0) < nv))) ”
  &&  “ (ans <= nv) ”
  &&  “ (1 <= ans) ”
  &&  “ (hi <= nv) ”
  &&  “ (0 <= hi) ”
  &&  “ (lo <= (nv + 1 )) ”
  &&  “ (1 <= lo) ”
  &&  emp
).

Definition solver_entail_wit_13_split_goal_1 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (ec: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : ((Zlength (head_data_2)) = nv)) (PreH6 : ((Zlength (parent_data_2)) = nv)) (PreH7 : ((Zlength (order_data_2)) = nv)) (PreH8 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH11 : (Pre nv kv edges )) (PreH12 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH13 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH14 : (SearchState nv kv edges lo hi ans )),
  forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data_2 0)) /\ ((Znth j order_data_2 0) < nv)) /\ ((-1) <= (Znth j parent_data_2 0))) /\ ((Znth j parent_data_2 0) < nv)))
.

Definition solver_entail_wit_13_split_goal_2 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (ec: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : ((Zlength (head_data_2)) = nv)) (PreH6 : ((Zlength (parent_data_2)) = nv)) (PreH7 : ((Zlength (order_data_2)) = nv)) (PreH8 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH11 : (Pre nv kv edges )) (PreH12 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH13 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH14 : (SearchState nv kv edges lo hi ans )),
  (ans <= nv)
.

Definition solver_entail_wit_13_split_goal_3 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (ec: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : ((Zlength (head_data_2)) = nv)) (PreH6 : ((Zlength (parent_data_2)) = nv)) (PreH7 : ((Zlength (order_data_2)) = nv)) (PreH8 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH11 : (Pre nv kv edges )) (PreH12 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH13 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH14 : (SearchState nv kv edges lo hi ans )),
  (1 <= ans)
.

Definition solver_entail_wit_13_split_goal_4 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (ec: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : ((Zlength (head_data_2)) = nv)) (PreH6 : ((Zlength (parent_data_2)) = nv)) (PreH7 : ((Zlength (order_data_2)) = nv)) (PreH8 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH11 : (Pre nv kv edges )) (PreH12 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH13 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH14 : (SearchState nv kv edges lo hi ans )),
  (hi <= nv)
.

Definition solver_entail_wit_13_split_goal_5 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (ec: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : ((Zlength (head_data_2)) = nv)) (PreH6 : ((Zlength (parent_data_2)) = nv)) (PreH7 : ((Zlength (order_data_2)) = nv)) (PreH8 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH11 : (Pre nv kv edges )) (PreH12 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH13 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH14 : (SearchState nv kv edges lo hi ans )),
  (0 <= hi)
.

Definition solver_entail_wit_13_split_goal_6 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (ec: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : ((Zlength (head_data_2)) = nv)) (PreH6 : ((Zlength (parent_data_2)) = nv)) (PreH7 : ((Zlength (order_data_2)) = nv)) (PreH8 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH11 : (Pre nv kv edges )) (PreH12 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH13 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH14 : (SearchState nv kv edges lo hi ans )),
  (lo <= (nv + 1 ))
.

Definition solver_entail_wit_13_split_goal_7 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (ec: Z) (ans: Z) (hi: Z) (lo: Z) (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : ((Zlength (head_data_2)) = nv)) (PreH6 : ((Zlength (parent_data_2)) = nv)) (PreH7 : ((Zlength (order_data_2)) = nv)) (PreH8 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH10 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH11 : (Pre nv kv edges )) (PreH12 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH13 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH14 : (SearchState nv kv edges lo hi ans )),
  (1 <= lo)
.

Definition solver_entail_wit_14_1 :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p_2: Z) (to_p_2: Z) (next_p_2: Z) (parent_p_2: Z) (order_p_2: Z) (size_p_2: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data_2)) = nv)) (PreH14 : ((Zlength (parent_data_2)) = nv)) (PreH15 : ((Zlength (order_data_2)) = nv)) (PreH16 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data_2 0)) /\ ((Znth j order_data_2 0) < nv)) /\ ((-1) <= (Znth j parent_data_2 0))) /\ ((Znth j parent_data_2 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH21 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval <> 0)),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p_2)
  **  ((( &( "order" ) )) # Ptr  |-> order_p_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full parent_p_2 nv parent_data_2 )
  **  (IntArray.full order_p_2 nv order_data_2 )
  **  (IntArray.undef_full size_p_2 nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
|--
  EX (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (order_data: (@list Z)) (parent_data: (@list Z)) (head_data: (@list Z)),
  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= (((lo + hi ) ÷ 2 ) + 1 )) ”
  &&  “ ((((lo + hi ) ÷ 2 ) + 1 ) <= (nv + 1 )) ”
  &&  “ (0 <= hi) ”
  &&  “ (hi <= nv) ”
  &&  “ (1 <= ((lo + hi ) ÷ 2 )) ”
  &&  “ (((lo + hi ) ÷ 2 ) <= nv) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (parent_data)) = nv) ”
  &&  “ ((Zlength (order_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ (SearchState nv kv edges (((lo + hi ) ÷ 2 ) + 1 ) hi ((lo + hi ) ÷ 2 ) ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
) \/
(
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data_2)) = nv)) (PreH14 : ((Zlength (parent_data_2)) = nv)) (PreH15 : ((Zlength (order_data_2)) = nv)) (PreH16 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data_2 0)) /\ ((Znth j order_data_2 0) < nv)) /\ ((-1) <= (Znth j parent_data_2 0))) /\ ((Znth j parent_data_2 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH21 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval <> 0)),
  TT && emp 
|--
  “ (SearchState nv kv edges (((lo + hi ) ÷ 2 ) + 1 ) hi ((lo + hi ) ÷ 2 ) ) ”
  &&  “ (((lo + hi ) ÷ 2 ) <= nv) ”
  &&  “ (1 <= ((lo + hi ) ÷ 2 )) ”
  &&  “ ((((lo + hi ) ÷ 2 ) + 1 ) <= (nv + 1 )) ”
  &&  “ (1 <= (((lo + hi ) ÷ 2 ) + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_14_1_split_goal_1 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data_2)) = nv)) (PreH14 : ((Zlength (parent_data_2)) = nv)) (PreH15 : ((Zlength (order_data_2)) = nv)) (PreH16 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data_2 0)) /\ ((Znth j order_data_2 0) < nv)) /\ ((-1) <= (Znth j parent_data_2 0))) /\ ((Znth j parent_data_2 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH21 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval <> 0)),
  (SearchState nv kv edges (((lo + hi ) ÷ 2 ) + 1 ) hi ((lo + hi ) ÷ 2 ) )
.

Definition solver_entail_wit_14_1_split_goal_2 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data_2)) = nv)) (PreH14 : ((Zlength (parent_data_2)) = nv)) (PreH15 : ((Zlength (order_data_2)) = nv)) (PreH16 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data_2 0)) /\ ((Znth j order_data_2 0) < nv)) /\ ((-1) <= (Znth j parent_data_2 0))) /\ ((Znth j parent_data_2 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH21 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval <> 0)),
  (((lo + hi ) ÷ 2 ) <= nv)
.

Definition solver_entail_wit_14_1_split_goal_3 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data_2)) = nv)) (PreH14 : ((Zlength (parent_data_2)) = nv)) (PreH15 : ((Zlength (order_data_2)) = nv)) (PreH16 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data_2 0)) /\ ((Znth j order_data_2 0) < nv)) /\ ((-1) <= (Znth j parent_data_2 0))) /\ ((Znth j parent_data_2 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH21 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval <> 0)),
  (1 <= ((lo + hi ) ÷ 2 ))
.

Definition solver_entail_wit_14_1_split_goal_4 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data_2)) = nv)) (PreH14 : ((Zlength (parent_data_2)) = nv)) (PreH15 : ((Zlength (order_data_2)) = nv)) (PreH16 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data_2 0)) /\ ((Znth j order_data_2 0) < nv)) /\ ((-1) <= (Znth j parent_data_2 0))) /\ ((Znth j parent_data_2 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH21 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval <> 0)),
  ((((lo + hi ) ÷ 2 ) + 1 ) <= (nv + 1 ))
.

Definition solver_entail_wit_14_1_split_goal_5 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data_2)) = nv)) (PreH14 : ((Zlength (parent_data_2)) = nv)) (PreH15 : ((Zlength (order_data_2)) = nv)) (PreH16 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data_2 0)) /\ ((Znth j order_data_2 0) < nv)) /\ ((-1) <= (Znth j parent_data_2 0))) /\ ((Znth j parent_data_2 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH21 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval <> 0)),
  (1 <= (((lo + hi ) ÷ 2 ) + 1 ))
.

Definition solver_entail_wit_14_2 :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p_2: Z) (to_p_2: Z) (next_p_2: Z) (parent_p_2: Z) (order_p_2: Z) (size_p_2: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data_2)) = nv)) (PreH14 : ((Zlength (parent_data_2)) = nv)) (PreH15 : ((Zlength (order_data_2)) = nv)) (PreH16 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data_2 0)) /\ ((Znth j order_data_2 0) < nv)) /\ ((-1) <= (Znth j parent_data_2 0))) /\ ((Znth j parent_data_2 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH21 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval = 0)),
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p_2)
  **  ((( &( "order" ) )) # Ptr  |-> order_p_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full parent_p_2 nv parent_data_2 )
  **  (IntArray.full order_p_2 nv order_data_2 )
  **  (IntArray.undef_full size_p_2 nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
|--
  EX (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (order_data: (@list Z)) (parent_data: (@list Z)) (head_data: (@list Z)),
  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= lo) ”
  &&  “ (lo <= (nv + 1 )) ”
  &&  “ (0 <= (((lo + hi ) ÷ 2 ) - 1 )) ”
  &&  “ ((((lo + hi ) ÷ 2 ) - 1 ) <= nv) ”
  &&  “ (1 <= ans) ”
  &&  “ (ans <= nv) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (parent_data)) = nv) ”
  &&  “ ((Zlength (order_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ (SearchState nv kv edges lo (((lo + hi ) ÷ 2 ) - 1 ) ans ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
) \/
(
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data_2)) = nv)) (PreH14 : ((Zlength (parent_data_2)) = nv)) (PreH15 : ((Zlength (order_data_2)) = nv)) (PreH16 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data_2 0)) /\ ((Znth j order_data_2 0) < nv)) /\ ((-1) <= (Znth j parent_data_2 0))) /\ ((Znth j parent_data_2 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH21 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval = 0)),
  TT && emp 
|--
  “ (SearchState nv kv edges lo (((lo + hi ) ÷ 2 ) - 1 ) ans ) ”
  &&  “ ((((lo + hi ) ÷ 2 ) - 1 ) <= nv) ”
  &&  “ (0 <= (((lo + hi ) ÷ 2 ) - 1 )) ”
  &&  emp
).

Definition solver_entail_wit_14_2_split_goal_1 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data_2)) = nv)) (PreH14 : ((Zlength (parent_data_2)) = nv)) (PreH15 : ((Zlength (order_data_2)) = nv)) (PreH16 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data_2 0)) /\ ((Znth j order_data_2 0) < nv)) /\ ((-1) <= (Znth j parent_data_2 0))) /\ ((Znth j parent_data_2 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH21 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval = 0)),
  (SearchState nv kv edges lo (((lo + hi ) ÷ 2 ) - 1 ) ans )
.

Definition solver_entail_wit_14_2_split_goal_2 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data_2)) = nv)) (PreH14 : ((Zlength (parent_data_2)) = nv)) (PreH15 : ((Zlength (order_data_2)) = nv)) (PreH16 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data_2 0)) /\ ((Znth j order_data_2 0) < nv)) /\ ((-1) <= (Znth j parent_data_2 0))) /\ ((Znth j parent_data_2 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH21 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval = 0)),
  ((((lo + hi ) ÷ 2 ) - 1 ) <= nv)
.

Definition solver_entail_wit_14_2_split_goal_3 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (parent_data_2: (@list Z)) (order_data_2: (@list Z)) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval <> 0) <-> (ThresholdFeasible nv kv edges ((lo + hi ) ÷ 2 ) ))) (PreH4 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data_2 0)) /\ ((Znth j_2 order_data_2 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data_2 0))) /\ ((Znth j_2 parent_data_2 0) < nv)))) (PreH5 : (lo <= hi)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= lo)) (PreH8 : (lo <= (nv + 1 ))) (PreH9 : (0 <= hi)) (PreH10 : (hi <= nv)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= nv)) (PreH13 : ((Zlength (head_data_2)) = nv)) (PreH14 : ((Zlength (parent_data_2)) = nv)) (PreH15 : ((Zlength (order_data_2)) = nv)) (PreH16 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH18 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data_2 0)) /\ ((Znth j order_data_2 0) < nv)) /\ ((-1) <= (Znth j parent_data_2 0))) /\ ((Znth j parent_data_2 0) < nv)))) (PreH19 : (Pre nv kv edges )) (PreH20 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH21 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH22 : (SearchState nv kv edges lo hi ans )) (PreH23 : (retval = 0)),
  (0 <= (((lo + hi ) ÷ 2 ) - 1 ))
.

Definition solver_entail_wit_15 :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (size_p_2: Z) (order_p_2: Z) (parent_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (order_data_2: (@list Z)) (parent_data_2: (@list Z)) (head_data_2: (@list Z)) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (PreH1 : (lo > hi)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= lo)) (PreH4 : (lo <= (nv + 1 ))) (PreH5 : (0 <= hi)) (PreH6 : (hi <= nv)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= nv)) (PreH9 : ((Zlength (head_data_2)) = nv)) (PreH10 : ((Zlength (parent_data_2)) = nv)) (PreH11 : ((Zlength (order_data_2)) = nv)) (PreH12 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data_2 0)) /\ ((Znth j order_data_2 0) < nv)) /\ ((-1) <= (Znth j parent_data_2 0))) /\ ((Znth j parent_data_2 0) < nv)))) (PreH15 : (Pre nv kv edges )) (PreH16 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH17 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH18 : (SearchState nv kv edges lo hi ans )),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p_2)
  **  ((( &( "order" ) )) # Ptr  |-> order_p_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full parent_p_2 nv parent_data_2 )
  **  (IntArray.full order_p_2 nv order_data_2 )
  **  (IntArray.undef_full size_p_2 nv )
|--
  EX (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (order_data: (@list Z)) (parent_data: (@list Z)) (head_data: (@list Z)),
  “ (Spec nv kv edges ans ) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= lo) ”
  &&  “ (lo <= (nv + 1 )) ”
  &&  “ (0 <= hi) ”
  &&  “ (hi < lo) ”
  &&  “ (hi <= nv) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (parent_data)) = nv) ”
  &&  “ ((Zlength (order_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
) \/
(
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (order_data_2: (@list Z)) (parent_data_2: (@list Z)) (head_data_2: (@list Z)) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (PreH1 : (lo > hi)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= lo)) (PreH4 : (lo <= (nv + 1 ))) (PreH5 : (0 <= hi)) (PreH6 : (hi <= nv)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= nv)) (PreH9 : ((Zlength (head_data_2)) = nv)) (PreH10 : ((Zlength (parent_data_2)) = nv)) (PreH11 : ((Zlength (order_data_2)) = nv)) (PreH12 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data_2 0)) /\ ((Znth j order_data_2 0) < nv)) /\ ((-1) <= (Znth j parent_data_2 0))) /\ ((Znth j parent_data_2 0) < nv)))) (PreH15 : (Pre nv kv edges )) (PreH16 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH17 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH18 : (SearchState nv kv edges lo hi ans )),
  TT && emp 
|--
  “ (Spec nv kv edges ans ) ”
  &&  emp
).

Definition solver_entail_wit_15_split_goal_1 :=
forall (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (next_data_2: (@list Z)) (to_data_2: (@list Z)) (order_data_2: (@list Z)) (parent_data_2: (@list Z)) (head_data_2: (@list Z)) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (PreH1 : (lo > hi)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= lo)) (PreH4 : (lo <= (nv + 1 ))) (PreH5 : (0 <= hi)) (PreH6 : (hi <= nv)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= nv)) (PreH9 : ((Zlength (head_data_2)) = nv)) (PreH10 : ((Zlength (parent_data_2)) = nv)) (PreH11 : ((Zlength (order_data_2)) = nv)) (PreH12 : ((Zlength (to_data_2)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data_2)) = ((2 * nv ) - 2 ))) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data_2 0)) /\ ((Znth j order_data_2 0) < nv)) /\ ((-1) <= (Znth j parent_data_2 0))) /\ ((Znth j parent_data_2 0) < nv)))) (PreH15 : (Pre nv kv edges )) (PreH16 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH17 : (RootedOrderModel nv edges parent_data_2 order_data_2 )) (PreH18 : (SearchState nv kv edges lo hi ans )),
  (Spec nv kv edges ans )
.

Definition solver_return_wit_1 :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (Spec nv kv edges ans )) (PreH2 : (Pre nv kv edges )) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= lo)) (PreH5 : (lo <= (nv + 1 ))) (PreH6 : (0 <= hi)) (PreH7 : (hi < lo)) (PreH8 : (hi <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
|--
  EX (size_after: Z) (order_after: Z) (parent_after: Z) (next_after: Z) (to_after: Z) (head_after: Z),
  “ (Spec nv kv edges ans ) ”
  &&  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_after)
  **  ((( &( "to" ) )) # Ptr  |-> to_after)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_after)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_after)
  **  ((( &( "order" ) )) # Ptr  |-> order_after)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_after)
) \/
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (Spec nv kv edges ans )) (PreH2 : (Pre nv kv edges )) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= lo)) (PreH5 : (lo <= (nv + 1 ))) (PreH6 : (0 <= hi)) (PreH7 : (hi < lo)) (PreH8 : (hi <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
|--
  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
).

Definition solver_return_wit_1_split_goal_spatial :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (Spec nv kv edges ans )) (PreH2 : (Pre nv kv edges )) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= lo)) (PreH5 : (lo <= (nv + 1 ))) (PreH6 : (0 <= hi)) (PreH7 : (hi < lo)) (PreH8 : (hi <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
|--
  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
.

Definition solver_partial_solve_wit_1_pure :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (next_before: Z) (to_before: Z) (head_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) __default__Prod_Z_Z (PreH1 : (1 <= kv)) (PreH2 : (kv < nv)) (PreH3 : (nv <= 100000)) (PreH4 : ((Zlength (edges)) = (nv - 1 ))) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH6 : (Pre nv kv edges )) (PreH7 : (nn_pre = nv)) (PreH8 : (kk_pre = kv)) (PreH9 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH10 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH11 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "kk" ) )) # Int  |-> kk_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_before)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_before)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ (0 <= nn_pre) ”
  &&  “ ((nn_pre * sizeof(INT) ) = (nn_pre * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_1_aux :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (next_before: Z) (to_before: Z) (head_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) __default__Prod_Z_Z (PreH1 : (1 <= kv)) (PreH2 : (kv < nv)) (PreH3 : (nv <= 100000)) (PreH4 : ((Zlength (edges)) = (nv - 1 ))) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH6 : (Pre nv kv edges )) (PreH7 : (nn_pre = nv)) (PreH8 : (kk_pre = kv)) (PreH9 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH10 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH11 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_before)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_before)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ (0 <= nn_pre) ”
  &&  “ ((nn_pre * sizeof(INT) ) = (nn_pre * sizeof(INT) )) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ ((Zlength (edges)) = (nv - 1 )) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (nn_pre = nv) ”
  &&  “ (kk_pre = kv) ”
  &&  “ ((Zlength (eu_data)) = (Zlength (edges))) ”
  &&  “ ((Zlength (ev_data)) = (Zlength (edges))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_before)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_before)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (next_before: Z) (to_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : ((Zlength (edges)) = (nv - 1 ))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH7 : (Pre nv kv edges )) (PreH8 : (nn_pre = nv)) (PreH9 : (kk_pre = kv)) (PreH10 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH11 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH12 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.undef_full retval nn_pre )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "kk" ) )) # Int  |-> kk_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_before)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ (0 <= ((2 * nn_pre ) - 2 )) ”
  &&  “ ((((2 * nn_pre ) - 2 ) * sizeof(INT) ) = (((2 * nn_pre ) - 2 ) * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_2_aux :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (next_before: Z) (to_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : ((Zlength (edges)) = (nv - 1 ))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH7 : (Pre nv kv edges )) (PreH8 : (nn_pre = nv)) (PreH9 : (kk_pre = kv)) (PreH10 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH11 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH12 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.undef_full retval nn_pre )
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_before)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ (0 <= ((2 * nn_pre ) - 2 )) ”
  &&  “ ((((2 * nn_pre ) - 2 ) * sizeof(INT) ) = (((2 * nn_pre ) - 2 ) * sizeof(INT) )) ”
  &&  “ (retval <> 0) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ ((Zlength (edges)) = (nv - 1 )) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (nn_pre = nv) ”
  &&  “ (kk_pre = kv) ”
  &&  “ ((Zlength (eu_data)) = (Zlength (edges))) ”
  &&  “ ((Zlength (ev_data)) = (Zlength (edges))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (IntArray.undef_full retval nn_pre )
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_before)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3_pure :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (next_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) (retval_2: Z) __default__Prod_Z_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= kv)) (PreH4 : (kv < nv)) (PreH5 : (nv <= 100000)) (PreH6 : ((Zlength (edges)) = (nv - 1 ))) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH8 : (Pre nv kv edges )) (PreH9 : (nn_pre = nv)) (PreH10 : (kk_pre = kv)) (PreH11 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH12 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH13 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.undef_full retval_2 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval nn_pre )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "kk" ) )) # Int  |-> kk_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> retval_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_before)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ (0 <= ((2 * nn_pre ) - 2 )) ”
  &&  “ ((((2 * nn_pre ) - 2 ) * sizeof(INT) ) = (((2 * nn_pre ) - 2 ) * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_3_aux :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (next_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (nn_pre: Z) (kk_pre: Z) (eu_pre: Z) (ev_pre: Z) (retval: Z) (retval_2: Z) __default__Prod_Z_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= kv)) (PreH4 : (kv < nv)) (PreH5 : (nv <= 100000)) (PreH6 : ((Zlength (edges)) = (nv - 1 ))) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))))) (PreH8 : (Pre nv kv edges )) (PreH9 : (nn_pre = nv)) (PreH10 : (kk_pre = kv)) (PreH11 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH12 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH13 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.undef_full retval_2 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval nn_pre )
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> retval_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_before)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ (0 <= ((2 * nn_pre ) - 2 )) ”
  &&  “ ((((2 * nn_pre ) - 2 ) * sizeof(INT) ) = (((2 * nn_pre ) - 2 ) * sizeof(INT) )) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (retval <> 0) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ ((Zlength (edges)) = (nv - 1 )) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (edges)))) -> (((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ ((1 <= (snd ((Znth i edges __default__Prod_Z_Z)))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (nn_pre = nv) ”
  &&  “ (kk_pre = kv) ”
  &&  “ ((Zlength (eu_data)) = (Zlength (edges))) ”
  &&  “ ((Zlength (ev_data)) = (Zlength (edges))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (IntArray.undef_full retval_2 ((2 * nn_pre ) - 2 ) )
  **  (IntArray.undef_full retval nn_pre )
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int  |-> kk_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> retval_2)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_before)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
.

Definition solver_partial_solve_wit_3 := solver_partial_solve_wit_3_pure -> solver_partial_solve_wit_3_aux.

Definition solver_partial_solve_wit_4 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (head_init: (@list Z)) (i: Z) __default__Prod_Z_Z (PreH1 : (i < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= nv)) (PreH8 : ((Zlength (head_init)) = i)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.seg head_p 0 i head_init )
  **  (IntArray.undef_seg head_p i nv )
  **  (IntArray.undef_full to_p ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p ((2 * nv ) - 2 ) )
|--
  “ (i < nv) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= nv) ”
  &&  “ ((Zlength (head_init)) = i) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((head_p + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg head_p (i + 1 ) nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.seg head_p 0 i head_init )
  **  (IntArray.undef_full to_p ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p ((2 * nv ) - 2 ) )
.

Definition solver_partial_solve_wit_5 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (to_done)) = ec)) (PreH11 : ((Zlength (next_done)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 ec to_done )
  **  (IntArray.undef_seg to_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
|--
  “ ((i + 1 ) < nv) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (nv - 1 )) ”
  &&  “ (ec = (2 * i )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_done)) = ec) ”
  &&  “ ((Zlength (next_done)) = ec) ”
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ”
  &&  “ (CurrentEdgeFresh edges i ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((ev_pre + (i * sizeof(INT)))) # Int  |-> (Znth i ev_data 0))
  **  (IntArray.missing_i ev_pre i 0 (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 ec to_done )
  **  (IntArray.undef_seg to_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
.

Definition solver_partial_solve_wit_6 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (to_done)) = ec)) (PreH11 : ((Zlength (next_done)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 ec to_done )
  **  (IntArray.undef_seg to_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
|--
  “ ((i + 1 ) < nv) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (nv - 1 )) ”
  &&  “ (ec = (2 * i )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_done)) = ec) ”
  &&  “ ((Zlength (next_done)) = ec) ”
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ”
  &&  “ (CurrentEdgeFresh edges i ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((eu_pre + (i * sizeof(INT)))) # Int  |-> (Znth i eu_data 0))
  **  (IntArray.missing_i eu_pre i 0 (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 ec to_done )
  **  (IntArray.undef_seg to_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
.

Definition solver_partial_solve_wit_7 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (to_done)) = ec)) (PreH11 : ((Zlength (next_done)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 ec to_done )
  **  (IntArray.undef_seg to_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
|--
  “ ((i + 1 ) < nv) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (nv - 1 )) ”
  &&  “ (ec = (2 * i )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_done)) = ec) ”
  &&  “ ((Zlength (next_done)) = ec) ”
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ”
  &&  “ (CurrentEdgeFresh edges i ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((to_p + (ec * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg to_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 ec to_done )
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
.

Definition solver_partial_solve_wit_8 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (to_done)) = ec)) (PreH11 : ((Zlength (next_done)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.seg to_p 0 (ec + 1 ) (app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
|--
  “ ((i + 1 ) < nv) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (nv - 1 )) ”
  &&  “ (ec = (2 * i )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_done)) = ec) ”
  &&  “ ((Zlength (next_done)) = ec) ”
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ”
  &&  “ (CurrentEdgeFresh edges i ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((head_p + ((Znth i eu_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i eu_data 0) head_data 0))
  **  (IntArray.missing_i head_p (Znth i eu_data 0) 0 nv head_data )
  **  (IntArray.seg to_p 0 (ec + 1 ) (app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
.

Definition solver_partial_solve_wit_9 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (to_done)) = ec)) (PreH11 : ((Zlength (next_done)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 (ec + 1 ) (app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
|--
  “ ((i + 1 ) < nv) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (nv - 1 )) ”
  &&  “ (ec = (2 * i )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_done)) = ec) ”
  &&  “ ((Zlength (next_done)) = ec) ”
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ”
  &&  “ (CurrentEdgeFresh edges i ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((next_p + (ec * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg next_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 (ec + 1 ) (app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.seg next_p 0 ec next_done )
.

Definition solver_partial_solve_wit_10 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (to_done)) = ec)) (PreH11 : ((Zlength (next_done)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.seg next_p 0 (ec + 1 ) (app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 (ec + 1 ) (app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ ((i + 1 ) < nv) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (nv - 1 )) ”
  &&  “ (ec = (2 * i )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_done)) = ec) ”
  &&  “ ((Zlength (next_done)) = ec) ”
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ”
  &&  “ (CurrentEdgeFresh edges i ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((head_p + ((Znth i eu_data 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i head_p (Znth i eu_data 0) 0 nv head_data )
  **  (IntArray.seg next_p 0 (ec + 1 ) (app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 (ec + 1 ) (app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
.

Definition solver_partial_solve_wit_11 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (to_done)) = ec)) (PreH11 : ((Zlength (next_done)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.full head_p nv (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) )
  **  (IntArray.seg next_p 0 (ec + 1 ) (app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 (ec + 1 ) (app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ ((i + 1 ) < nv) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (nv - 1 )) ”
  &&  “ (ec = (2 * i )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_done)) = ec) ”
  &&  “ ((Zlength (next_done)) = ec) ”
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ”
  &&  “ (CurrentEdgeFresh edges i ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((to_p + ((ec + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) )
  **  (IntArray.seg next_p 0 (ec + 1 ) (app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 (ec + 1 ) (app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z))))) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
.

Definition solver_partial_solve_wit_12 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (to_done)) = ec)) (PreH11 : ((Zlength (next_done)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) )
  **  (IntArray.seg next_p 0 (ec + 1 ) (app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ ((i + 1 ) < nv) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (nv - 1 )) ”
  &&  “ (ec = (2 * i )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_done)) = ec) ”
  &&  “ ((Zlength (next_done)) = ec) ”
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ”
  &&  “ (CurrentEdgeFresh edges i ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((head_p + ((Znth i ev_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0))
  **  (IntArray.missing_i head_p (Znth i ev_data 0) 0 nv (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 (ec + 1 ) (app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
.

Definition solver_partial_solve_wit_13 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (to_done)) = ec)) (PreH11 : ((Zlength (next_done)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.full head_p nv (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 (ec + 1 ) (app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ ((i + 1 ) < nv) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (nv - 1 )) ”
  &&  “ (ec = (2 * i )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_done)) = ec) ”
  &&  “ ((Zlength (next_done)) = ec) ”
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ”
  &&  “ (CurrentEdgeFresh edges i ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((next_p + ((ec + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 (ec + 1 ) (app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z))))) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
.

Definition solver_partial_solve_wit_14 :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z) __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (to_done)) = ec)) (PreH11 : ((Zlength (next_done)) = ec)) (PreH12 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH13 : (CurrentEdgeFresh edges i )) (PreH14 : forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))),
  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
|--
  “ ((i + 1 ) < nv) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (nv - 1 )) ”
  &&  “ (ec = (2 * i )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_done)) = ec) ”
  &&  “ ((Zlength (next_done)) = ec) ”
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ”
  &&  “ (CurrentEdgeFresh edges i ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((head_p + ((Znth i ev_data 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i head_p (Znth i ev_data 0) 0 nv (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
.

Definition solver_partial_solve_wit_15_pure :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (ec: Z) (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH7 : ((Zlength (head_data)) = nv)) (PreH8 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (0 <= nv) ”
  &&  “ ((nv * sizeof(INT) ) = (nv * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_15_aux :=
forall (size_before: Z) (order_before: Z) (parent_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (ec: Z) (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (1 <= kv)) (PreH3 : (kv < nv)) (PreH4 : (nv <= 100000)) (PreH5 : (Pre nv kv edges )) (PreH6 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH7 : ((Zlength (head_data)) = nv)) (PreH8 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (0 <= nv) ”
  &&  “ ((nv * sizeof(INT) ) = (nv * sizeof(INT) )) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_before)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
.

Definition solver_partial_solve_wit_15 := solver_partial_solve_wit_15_pure -> solver_partial_solve_wit_15_aux.

Definition solver_partial_solve_wit_16_pure :=
forall (size_before: Z) (order_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (ec: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= kv)) (PreH4 : (kv < nv)) (PreH5 : (nv <= 100000)) (PreH6 : (Pre nv kv edges )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH8 : ((Zlength (head_data)) = nv)) (PreH9 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH10 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> retval)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (0 <= nv) ”
  &&  “ ((nv * sizeof(INT) ) = (nv * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_16_aux :=
forall (size_before: Z) (order_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (ec: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= kv)) (PreH4 : (kv < nv)) (PreH5 : (nv <= 100000)) (PreH6 : (Pre nv kv edges )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH8 : ((Zlength (head_data)) = nv)) (PreH9 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH10 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (IntArray.undef_full retval nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> retval)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (0 <= nv) ”
  &&  “ ((nv * sizeof(INT) ) = (nv * sizeof(INT) )) ”
  &&  “ (retval <> 0) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  (IntArray.undef_full retval nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> retval)
  **  ((( &( "order" ) )) # Ptr  |-> order_before)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
.

Definition solver_partial_solve_wit_16 := solver_partial_solve_wit_16_pure -> solver_partial_solve_wit_16_aux.

Definition solver_partial_solve_wit_17_pure :=
forall (size_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= kv)) (PreH5 : (kv < nv)) (PreH6 : (nv <= 100000)) (PreH7 : (Pre nv kv edges )) (PreH8 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH11 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (IntArray.undef_full retval_2 nv )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> retval)
  **  ((( &( "order" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (0 <= nv) ”
  &&  “ ((nv * sizeof(INT) ) = (nv * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_17_aux :=
forall (size_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= kv)) (PreH5 : (kv < nv)) (PreH6 : (nv <= 100000)) (PreH7 : (Pre nv kv edges )) (PreH8 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH11 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (IntArray.undef_full retval_2 nv )
  **  (IntArray.undef_full retval nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> retval)
  **  ((( &( "order" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (0 <= nv) ”
  &&  “ ((nv * sizeof(INT) ) = (nv * sizeof(INT) )) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (retval <> 0) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  (IntArray.undef_full retval_2 nv )
  **  (IntArray.undef_full retval nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> retval)
  **  ((( &( "order" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_before)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
.

Definition solver_partial_solve_wit_17 := solver_partial_solve_wit_17_pure -> solver_partial_solve_wit_17_aux.

Definition solver_partial_solve_wit_18 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (cells: (@list (@option Z))) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (FreshSizeCells nv cells )) (PreH3 : ((Zlength (cells)) = nv)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= kv)) (PreH8 : (kv < nv)) (PreH9 : (nv <= 100000)) (PreH10 : (Pre nv kv edges )) (PreH11 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH12 : ((Zlength (head_data)) = nv)) (PreH13 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (IntArray.mixed_full retval_3 nv cells )
  **  (IntArray.undef_full retval_2 nv )
  **  (IntArray.undef_full retval nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> retval)
  **  ((( &( "order" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> retval_3)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (retval_3 <> 0) ”
  &&  “ (FreshSizeCells nv cells ) ”
  &&  “ ((Zlength (cells)) = nv) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (retval <> 0) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  (((retval_2 + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg retval_2 1 nv )
  **  (IntArray.mixed_full retval_3 nv cells )
  **  (IntArray.undef_full retval nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> retval)
  **  ((( &( "order" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> retval_3)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
.

Definition solver_partial_solve_wit_19 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (cells: (@list (@option Z))) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (FreshSizeCells nv cells )) (PreH3 : ((Zlength (cells)) = nv)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (ec = ((2 * nv ) - 2 ))) (PreH7 : (1 <= kv)) (PreH8 : (kv < nv)) (PreH9 : (nv <= 100000)) (PreH10 : (Pre nv kv edges )) (PreH11 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH12 : ((Zlength (head_data)) = nv)) (PreH13 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (((retval_2 + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg retval_2 1 nv )
  **  (IntArray.mixed_full retval_3 nv cells )
  **  (IntArray.undef_full retval nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> retval)
  **  ((( &( "order" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> retval_3)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
|--
  “ (retval_3 <> 0) ”
  &&  “ (FreshSizeCells nv cells ) ”
  &&  “ ((Zlength (cells)) = nv) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (retval <> 0) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  (((retval + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg retval 1 nv )
  **  (((retval_2 + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg retval_2 1 nv )
  **  (IntArray.mixed_full retval_3 nv cells )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> retval)
  **  ((( &( "order" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size_sub" ) )) # Ptr  |-> retval_3)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
.

Definition solver_partial_solve_wit_20 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (i: Z) (top: Z) (ec: Z) __default__App_option_Z (PreH1 : (i < top)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= top)) (PreH4 : (top <= nv)) (PreH5 : (0 <= i)) (PreH6 : (i <= top)) (PreH7 : ((Zlength (head_data)) = nv)) (PreH8 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH9 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH10 : ((Zlength (order_data)) = top)) (PreH11 : ((Zlength (parent_cells)) = nv)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH13 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH14 : (Pre nv kv edges )) (PreH15 : (TreeAttachmentCut edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (TraversalEntryState nv edges i order_data parent_cells )),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ (i < top) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= top) ”
  &&  “ (top <= nv) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= top) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (order_data)) = top) ”
  &&  “ ((Zlength (parent_cells)) = nv) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 )))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (TreeAttachmentCut edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (TraversalEntryState nv edges i order_data parent_cells ) ”
  &&  (((order_p + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) order_data 0))
  **  (IntArray.missing_i order_p i 0 top order_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
.

Definition solver_partial_solve_wit_21 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (order_data: (@list Z)) (parent_cells: (@list (@option Z))) (parent_v: Z) (pv: Z) (ec: Z) (i: Z) (top: Z) (v: Z) __default__App_option_Z (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i < top)) (PreH4 : (1 <= top)) (PreH5 : (top <= nv)) (PreH6 : (0 <= v)) (PreH7 : (v < nv)) (PreH8 : (v = (Znth i order_data 0))) (PreH9 : ((-1) <= parent_v)) (PreH10 : (parent_v < nv)) (PreH11 : ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v)))) (PreH12 : ((Zlength (head_data)) = nv)) (PreH13 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH14 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH15 : ((Zlength (order_data)) = top)) (PreH16 : ((Zlength (parent_cells)) = nv)) (PreH17 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH18 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH19 : (Pre nv kv edges )) (PreH20 : (TreeAttachmentCut edges )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH22 : (TraversalEntryState nv edges i order_data parent_cells )),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (((parent_p + (v * sizeof(INT)))) # Int  |-> parent_v)
  **  (IntArray.mixed_missing_i parent_p v 0 nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < top) ”
  &&  “ (1 <= top) ”
  &&  “ (top <= nv) ”
  &&  “ (0 <= v) ”
  &&  “ (v < nv) ”
  &&  “ (v = (Znth i order_data 0)) ”
  &&  “ ((-1) <= parent_v) ”
  &&  “ (parent_v < nv) ”
  &&  “ ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v))) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (order_data)) = top) ”
  &&  “ ((Zlength (parent_cells)) = nv) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 )))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (TreeAttachmentCut edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (TraversalEntryState nv edges i order_data parent_cells ) ”
  &&  (((head_p + (v * sizeof(INT)))) # Int  |-> (Znth v head_data 0))
  **  (IntArray.missing_i head_p v 0 nv head_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (((parent_p + (v * sizeof(INT)))) # Int  |-> parent_v)
  **  (IntArray.mixed_missing_i parent_p v 0 nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
.

Definition solver_partial_solve_wit_22 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (e: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (e <> (-1))) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i < top)) (PreH5 : (1 <= top)) (PreH6 : (top <= nv)) (PreH7 : (0 <= v)) (PreH8 : (v < nv)) (PreH9 : ((-1) <= parent_v)) (PreH10 : (parent_v < nv)) (PreH11 : (v = (Znth i order_data 0))) (PreH12 : ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v)))) (PreH13 : ((-1) <= e)) (PreH14 : (e < ((2 * nv ) - 2 ))) (PreH15 : ((Zlength (head_data)) = nv)) (PreH16 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH17 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH18 : ((Zlength (order_data)) = top)) (PreH19 : ((Zlength (parent_cells)) = nv)) (PreH20 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH21 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH22 : (Pre nv kv edges )) (PreH23 : (TreeAttachmentCut edges )) (PreH24 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH25 : (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e )) (PreH26 : (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv))),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ (e <> (-1)) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < top) ”
  &&  “ (1 <= top) ”
  &&  “ (top <= nv) ”
  &&  “ (0 <= v) ”
  &&  “ (v < nv) ”
  &&  “ ((-1) <= parent_v) ”
  &&  “ (parent_v < nv) ”
  &&  “ (v = (Znth i order_data 0)) ”
  &&  “ ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v))) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (order_data)) = top) ”
  &&  “ ((Zlength (parent_cells)) = nv) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 )))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (TreeAttachmentCut edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e ) ”
  &&  “ (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv)) ”
  &&  (((to_p + (e * sizeof(INT)))) # Int  |-> (Znth e to_data 0))
  **  (IntArray.missing_i to_p e 0 ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
.

Definition solver_partial_solve_wit_23 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (e: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (top < nv)) (PreH2 : (e <= INT_MAX)) (PreH3 : (parent_v <= INT_MAX)) (PreH4 : (v <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (ec <= INT_MAX)) (PreH7 : (kv <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (e >= INT_MIN)) (PreH10 : (parent_v >= INT_MIN)) (PreH11 : (v >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (kv >= INT_MIN)) (PreH15 : (nv >= INT_MIN)) (PreH16 : ((Znth e to_data 0) <> parent_v)) (PreH17 : (e <> (-1))) (PreH18 : (ec = ((2 * nv ) - 2 ))) (PreH19 : (0 <= i)) (PreH20 : (i < top)) (PreH21 : (1 <= top)) (PreH22 : (top <= nv)) (PreH23 : (0 <= v)) (PreH24 : (v < nv)) (PreH25 : ((-1) <= parent_v)) (PreH26 : (parent_v < nv)) (PreH27 : (v = (Znth i order_data 0))) (PreH28 : ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v)))) (PreH29 : ((-1) <= e)) (PreH30 : (e < ((2 * nv ) - 2 ))) (PreH31 : ((Zlength (head_data)) = nv)) (PreH32 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH33 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH34 : ((Zlength (order_data)) = top)) (PreH35 : ((Zlength (parent_cells)) = nv)) (PreH36 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH37 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH38 : (Pre nv kv edges )) (PreH39 : (TreeAttachmentCut edges )) (PreH40 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH41 : (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e )) (PreH42 : (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv))),
  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ (top < nv) ”
  &&  “ (e <= INT_MAX) ”
  &&  “ (parent_v <= INT_MAX) ”
  &&  “ (v <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (ec <= INT_MAX) ”
  &&  “ (kv <= INT_MAX) ”
  &&  “ (nv <= INT_MAX) ”
  &&  “ (e >= INT_MIN) ”
  &&  “ (parent_v >= INT_MIN) ”
  &&  “ (v >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (ec >= INT_MIN) ”
  &&  “ (kv >= INT_MIN) ”
  &&  “ (nv >= INT_MIN) ”
  &&  “ ((Znth e to_data 0) <> parent_v) ”
  &&  “ (e <> (-1)) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < top) ”
  &&  “ (1 <= top) ”
  &&  “ (top <= nv) ”
  &&  “ (0 <= v) ”
  &&  “ (v < nv) ”
  &&  “ ((-1) <= parent_v) ”
  &&  “ (parent_v < nv) ”
  &&  “ (v = (Znth i order_data 0)) ”
  &&  “ ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v))) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (order_data)) = top) ”
  &&  “ ((Zlength (parent_cells)) = nv) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 )))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (TreeAttachmentCut edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e ) ”
  &&  “ (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv)) ”
  &&  (((to_p + (e * sizeof(INT)))) # Int  |-> (Znth e to_data 0))
  **  (IntArray.missing_i to_p e 0 ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
.

Definition solver_partial_solve_wit_24 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (e: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (top < nv)) (PreH2 : (e <= INT_MAX)) (PreH3 : (parent_v <= INT_MAX)) (PreH4 : (v <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (ec <= INT_MAX)) (PreH7 : (kv <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (e >= INT_MIN)) (PreH10 : (parent_v >= INT_MIN)) (PreH11 : (v >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (kv >= INT_MIN)) (PreH15 : (nv >= INT_MIN)) (PreH16 : ((Znth e to_data 0) <> parent_v)) (PreH17 : (e <> (-1))) (PreH18 : (ec = ((2 * nv ) - 2 ))) (PreH19 : (0 <= i)) (PreH20 : (i < top)) (PreH21 : (1 <= top)) (PreH22 : (top <= nv)) (PreH23 : (0 <= v)) (PreH24 : (v < nv)) (PreH25 : ((-1) <= parent_v)) (PreH26 : (parent_v < nv)) (PreH27 : (v = (Znth i order_data 0))) (PreH28 : ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v)))) (PreH29 : ((-1) <= e)) (PreH30 : (e < ((2 * nv ) - 2 ))) (PreH31 : ((Zlength (head_data)) = nv)) (PreH32 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH33 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH34 : ((Zlength (order_data)) = top)) (PreH35 : ((Zlength (parent_cells)) = nv)) (PreH36 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH37 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH38 : (Pre nv kv edges )) (PreH39 : (TreeAttachmentCut edges )) (PreH40 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH41 : (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e )) (PreH42 : (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv))),
  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ (top < nv) ”
  &&  “ (e <= INT_MAX) ”
  &&  “ (parent_v <= INT_MAX) ”
  &&  “ (v <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (ec <= INT_MAX) ”
  &&  “ (kv <= INT_MAX) ”
  &&  “ (nv <= INT_MAX) ”
  &&  “ (e >= INT_MIN) ”
  &&  “ (parent_v >= INT_MIN) ”
  &&  “ (v >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (ec >= INT_MIN) ”
  &&  “ (kv >= INT_MIN) ”
  &&  “ (nv >= INT_MIN) ”
  &&  “ ((Znth e to_data 0) <> parent_v) ”
  &&  “ (e <> (-1)) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < top) ”
  &&  “ (1 <= top) ”
  &&  “ (top <= nv) ”
  &&  “ (0 <= v) ”
  &&  “ (v < nv) ”
  &&  “ ((-1) <= parent_v) ”
  &&  “ (parent_v < nv) ”
  &&  “ (v = (Znth i order_data 0)) ”
  &&  “ ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v))) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (order_data)) = top) ”
  &&  “ ((Zlength (parent_cells)) = nv) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 )))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (TreeAttachmentCut edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e ) ”
  &&  “ (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv)) ”
  &&  (((parent_p + ((Znth e to_data 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i parent_p (Znth e to_data 0) 0 nv parent_cells )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
.

Definition solver_partial_solve_wit_25 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (e: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (top < nv)) (PreH2 : (e <= INT_MAX)) (PreH3 : (parent_v <= INT_MAX)) (PreH4 : (v <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (ec <= INT_MAX)) (PreH7 : (kv <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (e >= INT_MIN)) (PreH10 : (parent_v >= INT_MIN)) (PreH11 : (v >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (kv >= INT_MIN)) (PreH15 : (nv >= INT_MIN)) (PreH16 : ((Znth e to_data 0) <> parent_v)) (PreH17 : (e <> (-1))) (PreH18 : (ec = ((2 * nv ) - 2 ))) (PreH19 : (0 <= i)) (PreH20 : (i < top)) (PreH21 : (1 <= top)) (PreH22 : (top <= nv)) (PreH23 : (0 <= v)) (PreH24 : (v < nv)) (PreH25 : ((-1) <= parent_v)) (PreH26 : (parent_v < nv)) (PreH27 : (v = (Znth i order_data 0))) (PreH28 : ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v)))) (PreH29 : ((-1) <= e)) (PreH30 : (e < ((2 * nv ) - 2 ))) (PreH31 : ((Zlength (head_data)) = nv)) (PreH32 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH33 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH34 : ((Zlength (order_data)) = top)) (PreH35 : ((Zlength (parent_cells)) = nv)) (PreH36 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH37 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH38 : (Pre nv kv edges )) (PreH39 : (TreeAttachmentCut edges )) (PreH40 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH41 : (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e )) (PreH42 : (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv))),
  (IntArray.mixed_full parent_p nv (replace_Znth ((Znth e to_data 0)) ((Some (v))) (parent_cells)) )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ (top < nv) ”
  &&  “ (e <= INT_MAX) ”
  &&  “ (parent_v <= INT_MAX) ”
  &&  “ (v <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (ec <= INT_MAX) ”
  &&  “ (kv <= INT_MAX) ”
  &&  “ (nv <= INT_MAX) ”
  &&  “ (e >= INT_MIN) ”
  &&  “ (parent_v >= INT_MIN) ”
  &&  “ (v >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (ec >= INT_MIN) ”
  &&  “ (kv >= INT_MIN) ”
  &&  “ (nv >= INT_MIN) ”
  &&  “ ((Znth e to_data 0) <> parent_v) ”
  &&  “ (e <> (-1)) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < top) ”
  &&  “ (1 <= top) ”
  &&  “ (top <= nv) ”
  &&  “ (0 <= v) ”
  &&  “ (v < nv) ”
  &&  “ ((-1) <= parent_v) ”
  &&  “ (parent_v < nv) ”
  &&  “ (v = (Znth i order_data 0)) ”
  &&  “ ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v))) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (order_data)) = top) ”
  &&  “ ((Zlength (parent_cells)) = nv) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 )))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (TreeAttachmentCut edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e ) ”
  &&  “ (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv)) ”
  &&  (((to_p + (e * sizeof(INT)))) # Int  |-> (Znth e to_data 0))
  **  (IntArray.missing_i to_p e 0 ((2 * nv ) - 2 ) to_data )
  **  (IntArray.mixed_full parent_p nv (replace_Znth ((Znth e to_data 0)) ((Some (v))) (parent_cells)) )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
.

Definition solver_partial_solve_wit_26 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (e: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (top < nv)) (PreH2 : (e <= INT_MAX)) (PreH3 : (parent_v <= INT_MAX)) (PreH4 : (v <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (ec <= INT_MAX)) (PreH7 : (kv <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (e >= INT_MIN)) (PreH10 : (parent_v >= INT_MIN)) (PreH11 : (v >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (kv >= INT_MIN)) (PreH15 : (nv >= INT_MIN)) (PreH16 : ((Znth e to_data 0) <> parent_v)) (PreH17 : (e <> (-1))) (PreH18 : (ec = ((2 * nv ) - 2 ))) (PreH19 : (0 <= i)) (PreH20 : (i < top)) (PreH21 : (1 <= top)) (PreH22 : (top <= nv)) (PreH23 : (0 <= v)) (PreH24 : (v < nv)) (PreH25 : ((-1) <= parent_v)) (PreH26 : (parent_v < nv)) (PreH27 : (v = (Znth i order_data 0))) (PreH28 : ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v)))) (PreH29 : ((-1) <= e)) (PreH30 : (e < ((2 * nv ) - 2 ))) (PreH31 : ((Zlength (head_data)) = nv)) (PreH32 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH33 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH34 : ((Zlength (order_data)) = top)) (PreH35 : ((Zlength (parent_cells)) = nv)) (PreH36 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH37 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH38 : (Pre nv kv edges )) (PreH39 : (TreeAttachmentCut edges )) (PreH40 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH41 : (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e )) (PreH42 : (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv))),
  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.mixed_full parent_p nv (replace_Znth ((Znth e to_data 0)) ((Some (v))) (parent_cells)) )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ (top < nv) ”
  &&  “ (e <= INT_MAX) ”
  &&  “ (parent_v <= INT_MAX) ”
  &&  “ (v <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (ec <= INT_MAX) ”
  &&  “ (kv <= INT_MAX) ”
  &&  “ (nv <= INT_MAX) ”
  &&  “ (e >= INT_MIN) ”
  &&  “ (parent_v >= INT_MIN) ”
  &&  “ (v >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (ec >= INT_MIN) ”
  &&  “ (kv >= INT_MIN) ”
  &&  “ (nv >= INT_MIN) ”
  &&  “ ((Znth e to_data 0) <> parent_v) ”
  &&  “ (e <> (-1)) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < top) ”
  &&  “ (1 <= top) ”
  &&  “ (top <= nv) ”
  &&  “ (0 <= v) ”
  &&  “ (v < nv) ”
  &&  “ ((-1) <= parent_v) ”
  &&  “ (parent_v < nv) ”
  &&  “ (v = (Znth i order_data 0)) ”
  &&  “ ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v))) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (order_data)) = top) ”
  &&  “ ((Zlength (parent_cells)) = nv) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 )))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (TreeAttachmentCut edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e ) ”
  &&  “ (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv)) ”
  &&  (((order_p + (top * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg order_p (top + 1 ) nv )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.mixed_full parent_p nv (replace_Znth ((Znth e to_data 0)) ((Some (v))) (parent_cells)) )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_full size_p nv )
.

Definition solver_partial_solve_wit_27 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (e: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : (top < nv)) (PreH2 : (e <= INT_MAX)) (PreH3 : (parent_v <= INT_MAX)) (PreH4 : (v <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (ec <= INT_MAX)) (PreH7 : (kv <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (e >= INT_MIN)) (PreH10 : (parent_v >= INT_MIN)) (PreH11 : (v >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (kv >= INT_MIN)) (PreH15 : (nv >= INT_MIN)) (PreH16 : ((Znth e to_data 0) <> parent_v)) (PreH17 : (e <> (-1))) (PreH18 : (ec = ((2 * nv ) - 2 ))) (PreH19 : (0 <= i)) (PreH20 : (i < top)) (PreH21 : (1 <= top)) (PreH22 : (top <= nv)) (PreH23 : (0 <= v)) (PreH24 : (v < nv)) (PreH25 : ((-1) <= parent_v)) (PreH26 : (parent_v < nv)) (PreH27 : (v = (Znth i order_data 0))) (PreH28 : ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v)))) (PreH29 : ((-1) <= e)) (PreH30 : (e < ((2 * nv ) - 2 ))) (PreH31 : ((Zlength (head_data)) = nv)) (PreH32 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH33 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH34 : ((Zlength (order_data)) = top)) (PreH35 : ((Zlength (parent_cells)) = nv)) (PreH36 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH37 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH38 : (Pre nv kv edges )) (PreH39 : (TreeAttachmentCut edges )) (PreH40 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH41 : (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e )) (PreH42 : (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv))),
  (IntArray.seg order_p 0 (top + 1 ) (app (order_data) ((cons ((Znth e to_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg order_p (top + 1 ) nv )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.mixed_full parent_p nv (replace_Znth ((Znth e to_data 0)) ((Some (v))) (parent_cells)) )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (top < nv) ”
  &&  “ (e <= INT_MAX) ”
  &&  “ (parent_v <= INT_MAX) ”
  &&  “ (v <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (ec <= INT_MAX) ”
  &&  “ (kv <= INT_MAX) ”
  &&  “ (nv <= INT_MAX) ”
  &&  “ (e >= INT_MIN) ”
  &&  “ (parent_v >= INT_MIN) ”
  &&  “ (v >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (ec >= INT_MIN) ”
  &&  “ (kv >= INT_MIN) ”
  &&  “ (nv >= INT_MIN) ”
  &&  “ ((Znth e to_data 0) <> parent_v) ”
  &&  “ (e <> (-1)) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < top) ”
  &&  “ (1 <= top) ”
  &&  “ (top <= nv) ”
  &&  “ (0 <= v) ”
  &&  “ (v < nv) ”
  &&  “ ((-1) <= parent_v) ”
  &&  “ (parent_v < nv) ”
  &&  “ (v = (Znth i order_data 0)) ”
  &&  “ ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v))) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (order_data)) = top) ”
  &&  “ ((Zlength (parent_cells)) = nv) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 )))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (TreeAttachmentCut edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e ) ”
  &&  “ (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv)) ”
  &&  (((next_p + (e * sizeof(INT)))) # Int  |-> (Znth e next_data 0))
  **  (IntArray.missing_i next_p e 0 ((2 * nv ) - 2 ) next_data )
  **  (IntArray.seg order_p 0 (top + 1 ) (app (order_data) ((cons ((Znth e to_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg order_p (top + 1 ) nv )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.mixed_full parent_p nv (replace_Znth ((Znth e to_data 0)) ((Some (v))) (parent_cells)) )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.undef_full size_p nv )
.

Definition solver_partial_solve_wit_28 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (pv: Z) (size_p: Z) (order_p: Z) (parent_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (next_data: (@list Z)) (to_data: (@list Z)) (head_data: (@list Z)) (e: Z) (parent_cells: (@list (@option Z))) (order_data: (@list Z)) (parent_v: Z) (v: Z) (top: Z) (i: Z) (ec: Z) __default__App_option_Z (PreH1 : ((Znth e to_data 0) = parent_v)) (PreH2 : (e <> (-1))) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (0 <= i)) (PreH5 : (i < top)) (PreH6 : (1 <= top)) (PreH7 : (top <= nv)) (PreH8 : (0 <= v)) (PreH9 : (v < nv)) (PreH10 : ((-1) <= parent_v)) (PreH11 : (parent_v < nv)) (PreH12 : (v = (Znth i order_data 0))) (PreH13 : ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v)))) (PreH14 : ((-1) <= e)) (PreH15 : (e < ((2 * nv ) - 2 ))) (PreH16 : ((Zlength (head_data)) = nv)) (PreH17 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH18 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH19 : ((Zlength (order_data)) = top)) (PreH20 : ((Zlength (parent_cells)) = nv)) (PreH21 : forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv))))) (PreH22 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 ))))) (PreH23 : (Pre nv kv edges )) (PreH24 : (TreeAttachmentCut edges )) (PreH25 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH26 : (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e )) (PreH27 : (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv))),
  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((Znth e to_data 0) = parent_v) ”
  &&  “ (e <> (-1)) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < top) ”
  &&  “ (1 <= top) ”
  &&  “ (top <= nv) ”
  &&  “ (0 <= v) ”
  &&  “ (v < nv) ”
  &&  “ ((-1) <= parent_v) ”
  &&  “ (parent_v < nv) ”
  &&  “ (v = (Znth i order_data 0)) ”
  &&  “ ((Znth v parent_cells __default__App_option_Z) = (Some (parent_v))) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (order_data)) = top) ”
  &&  “ ((Zlength (parent_cells)) = nv) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < top)) -> (((0 <= (Znth q order_data 0)) /\ ((Znth q order_data 0) < nv)) /\ exists (pv: Z), ((((Znth (Znth q order_data 0) parent_cells __default__App_option_Z) = (Some (pv))) /\ ((-1) <= pv)) /\ (pv < nv)))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < ((2 * nv ) - 2 ))) -> ((((0 <= (Znth q_2 to_data 0)) /\ ((Znth q_2 to_data 0) < nv)) /\ ((-1) <= (Znth q_2 next_data 0))) /\ ((Znth q_2 next_data 0) < ((2 * nv ) - 2 )))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (TreeAttachmentCut edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (TraversalAdjState nv edges i order_data parent_cells head_data to_data next_data v parent_v e ) ”
  &&  “ (((e <> (-1)) /\ ((Znth e to_data 0) <> parent_v)) -> (top < nv)) ”
  &&  (((next_p + (e * sizeof(INT)))) # Int  |-> (Znth e next_data 0))
  **  (IntArray.missing_i next_p e 0 ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.mixed_full parent_p nv parent_cells )
  **  (IntArray.seg order_p 0 top order_data )
  **  (IntArray.undef_seg order_p top nv )
  **  (IntArray.undef_full size_p nv )
.

Definition solver_partial_solve_wit_29_pure :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (lo <= hi)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= lo)) (PreH4 : (lo <= (nv + 1 ))) (PreH5 : (0 <= hi)) (PreH6 : (hi <= nv)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH15 : (Pre nv kv edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (RootedOrderModel nv edges parent_data order_data )) (PreH18 : (SearchState nv kv edges lo hi ans )),
  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (parent_data)) = nv) ”
  &&  “ ((Zlength (order_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
  &&  “ (nv <= 100000) ”
  &&  “ (kv < nv) ”
  &&  “ (1 <= kv) ”
  &&  “ (((lo + hi ) ÷ 2 ) <= nv) ”
  &&  “ (1 <= ((lo + hi ) ÷ 2 )) ”
) \/
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (ans <= INT_MAX)) (PreH2 : (hi <= INT_MAX)) (PreH3 : (lo <= INT_MAX)) (PreH4 : (ec <= INT_MAX)) (PreH5 : (kv <= INT_MAX)) (PreH6 : (nv <= INT_MAX)) (PreH7 : (((lo + hi ) ÷ 2 ) <= INT_MAX)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (hi >= INT_MIN)) (PreH10 : (lo >= INT_MIN)) (PreH11 : (ec >= INT_MIN)) (PreH12 : (kv >= INT_MIN)) (PreH13 : (nv >= INT_MIN)) (PreH14 : (((lo + hi ) ÷ 2 ) >= INT_MIN)) (PreH15 : (lo <= hi)) (PreH16 : (ec = ((2 * nv ) - 2 ))) (PreH17 : (1 <= lo)) (PreH18 : (lo <= (nv + 1 ))) (PreH19 : (0 <= hi)) (PreH20 : (hi <= nv)) (PreH21 : (1 <= ans)) (PreH22 : (ans <= nv)) (PreH23 : ((Zlength (head_data)) = nv)) (PreH24 : ((Zlength (parent_data)) = nv)) (PreH25 : ((Zlength (order_data)) = nv)) (PreH26 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH27 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH28 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH29 : (Pre nv kv edges )) (PreH30 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH31 : (RootedOrderModel nv edges parent_data order_data )) (PreH32 : (SearchState nv kv edges lo hi ans )),
  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (1 <= ((lo + hi ) ÷ 2 )) ”
  &&  “ (((lo + hi ) ÷ 2 ) <= nv) ”
  &&  “ (1 <= kv) ”
  &&  “ (kv < nv) ”
  &&  “ (nv <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
).

Definition solver_partial_solve_wit_29_pure_split_goal_1 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (ans <= INT_MAX)) (PreH2 : (hi <= INT_MAX)) (PreH3 : (lo <= INT_MAX)) (PreH4 : (ec <= INT_MAX)) (PreH5 : (kv <= INT_MAX)) (PreH6 : (nv <= INT_MAX)) (PreH7 : (((lo + hi ) ÷ 2 ) <= INT_MAX)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (hi >= INT_MIN)) (PreH10 : (lo >= INT_MIN)) (PreH11 : (ec >= INT_MIN)) (PreH12 : (kv >= INT_MIN)) (PreH13 : (nv >= INT_MIN)) (PreH14 : (((lo + hi ) ÷ 2 ) >= INT_MIN)) (PreH15 : (lo <= hi)) (PreH16 : (ec = ((2 * nv ) - 2 ))) (PreH17 : (1 <= lo)) (PreH18 : (lo <= (nv + 1 ))) (PreH19 : (0 <= hi)) (PreH20 : (hi <= nv)) (PreH21 : (1 <= ans)) (PreH22 : (ans <= nv)) (PreH23 : ((Zlength (head_data)) = nv)) (PreH24 : ((Zlength (parent_data)) = nv)) (PreH25 : ((Zlength (order_data)) = nv)) (PreH26 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH27 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH28 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH29 : (Pre nv kv edges )) (PreH30 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH31 : (RootedOrderModel nv edges parent_data order_data )) (PreH32 : (SearchState nv kv edges lo hi ans )),
  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (1 <= ((lo + hi ) ÷ 2 )) ”
.

Definition solver_partial_solve_wit_29_pure_split_goal_2 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (ans <= INT_MAX)) (PreH2 : (hi <= INT_MAX)) (PreH3 : (lo <= INT_MAX)) (PreH4 : (ec <= INT_MAX)) (PreH5 : (kv <= INT_MAX)) (PreH6 : (nv <= INT_MAX)) (PreH7 : (((lo + hi ) ÷ 2 ) <= INT_MAX)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (hi >= INT_MIN)) (PreH10 : (lo >= INT_MIN)) (PreH11 : (ec >= INT_MIN)) (PreH12 : (kv >= INT_MIN)) (PreH13 : (nv >= INT_MIN)) (PreH14 : (((lo + hi ) ÷ 2 ) >= INT_MIN)) (PreH15 : (lo <= hi)) (PreH16 : (ec = ((2 * nv ) - 2 ))) (PreH17 : (1 <= lo)) (PreH18 : (lo <= (nv + 1 ))) (PreH19 : (0 <= hi)) (PreH20 : (hi <= nv)) (PreH21 : (1 <= ans)) (PreH22 : (ans <= nv)) (PreH23 : ((Zlength (head_data)) = nv)) (PreH24 : ((Zlength (parent_data)) = nv)) (PreH25 : ((Zlength (order_data)) = nv)) (PreH26 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH27 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH28 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH29 : (Pre nv kv edges )) (PreH30 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH31 : (RootedOrderModel nv edges parent_data order_data )) (PreH32 : (SearchState nv kv edges lo hi ans )),
  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (((lo + hi ) ÷ 2 ) <= nv) ”
.

Definition solver_partial_solve_wit_29_pure_split_goal_3 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (ans <= INT_MAX)) (PreH2 : (hi <= INT_MAX)) (PreH3 : (lo <= INT_MAX)) (PreH4 : (ec <= INT_MAX)) (PreH5 : (kv <= INT_MAX)) (PreH6 : (nv <= INT_MAX)) (PreH7 : (((lo + hi ) ÷ 2 ) <= INT_MAX)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (hi >= INT_MIN)) (PreH10 : (lo >= INT_MIN)) (PreH11 : (ec >= INT_MIN)) (PreH12 : (kv >= INT_MIN)) (PreH13 : (nv >= INT_MIN)) (PreH14 : (((lo + hi ) ÷ 2 ) >= INT_MIN)) (PreH15 : (lo <= hi)) (PreH16 : (ec = ((2 * nv ) - 2 ))) (PreH17 : (1 <= lo)) (PreH18 : (lo <= (nv + 1 ))) (PreH19 : (0 <= hi)) (PreH20 : (hi <= nv)) (PreH21 : (1 <= ans)) (PreH22 : (ans <= nv)) (PreH23 : ((Zlength (head_data)) = nv)) (PreH24 : ((Zlength (parent_data)) = nv)) (PreH25 : ((Zlength (order_data)) = nv)) (PreH26 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH27 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH28 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH29 : (Pre nv kv edges )) (PreH30 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH31 : (RootedOrderModel nv edges parent_data order_data )) (PreH32 : (SearchState nv kv edges lo hi ans )),
  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (1 <= kv) ”
.

Definition solver_partial_solve_wit_29_pure_split_goal_4 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (ans <= INT_MAX)) (PreH2 : (hi <= INT_MAX)) (PreH3 : (lo <= INT_MAX)) (PreH4 : (ec <= INT_MAX)) (PreH5 : (kv <= INT_MAX)) (PreH6 : (nv <= INT_MAX)) (PreH7 : (((lo + hi ) ÷ 2 ) <= INT_MAX)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (hi >= INT_MIN)) (PreH10 : (lo >= INT_MIN)) (PreH11 : (ec >= INT_MIN)) (PreH12 : (kv >= INT_MIN)) (PreH13 : (nv >= INT_MIN)) (PreH14 : (((lo + hi ) ÷ 2 ) >= INT_MIN)) (PreH15 : (lo <= hi)) (PreH16 : (ec = ((2 * nv ) - 2 ))) (PreH17 : (1 <= lo)) (PreH18 : (lo <= (nv + 1 ))) (PreH19 : (0 <= hi)) (PreH20 : (hi <= nv)) (PreH21 : (1 <= ans)) (PreH22 : (ans <= nv)) (PreH23 : ((Zlength (head_data)) = nv)) (PreH24 : ((Zlength (parent_data)) = nv)) (PreH25 : ((Zlength (order_data)) = nv)) (PreH26 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH27 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH28 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH29 : (Pre nv kv edges )) (PreH30 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH31 : (RootedOrderModel nv edges parent_data order_data )) (PreH32 : (SearchState nv kv edges lo hi ans )),
  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (kv < nv) ”
.

Definition solver_partial_solve_wit_29_pure_split_goal_5 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (ans <= INT_MAX)) (PreH2 : (hi <= INT_MAX)) (PreH3 : (lo <= INT_MAX)) (PreH4 : (ec <= INT_MAX)) (PreH5 : (kv <= INT_MAX)) (PreH6 : (nv <= INT_MAX)) (PreH7 : (((lo + hi ) ÷ 2 ) <= INT_MAX)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (hi >= INT_MIN)) (PreH10 : (lo >= INT_MIN)) (PreH11 : (ec >= INT_MIN)) (PreH12 : (kv >= INT_MIN)) (PreH13 : (nv >= INT_MIN)) (PreH14 : (((lo + hi ) ÷ 2 ) >= INT_MIN)) (PreH15 : (lo <= hi)) (PreH16 : (ec = ((2 * nv ) - 2 ))) (PreH17 : (1 <= lo)) (PreH18 : (lo <= (nv + 1 ))) (PreH19 : (0 <= hi)) (PreH20 : (hi <= nv)) (PreH21 : (1 <= ans)) (PreH22 : (ans <= nv)) (PreH23 : ((Zlength (head_data)) = nv)) (PreH24 : ((Zlength (parent_data)) = nv)) (PreH25 : ((Zlength (order_data)) = nv)) (PreH26 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH27 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH28 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH29 : (Pre nv kv edges )) (PreH30 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH31 : (RootedOrderModel nv edges parent_data order_data )) (PreH32 : (SearchState nv kv edges lo hi ans )),
  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (nv <= 100000) ”
.

Definition solver_partial_solve_wit_29_pure_split_goal_6 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (ans <= INT_MAX)) (PreH2 : (hi <= INT_MAX)) (PreH3 : (lo <= INT_MAX)) (PreH4 : (ec <= INT_MAX)) (PreH5 : (kv <= INT_MAX)) (PreH6 : (nv <= INT_MAX)) (PreH7 : (((lo + hi ) ÷ 2 ) <= INT_MAX)) (PreH8 : (ans >= INT_MIN)) (PreH9 : (hi >= INT_MIN)) (PreH10 : (lo >= INT_MIN)) (PreH11 : (ec >= INT_MIN)) (PreH12 : (kv >= INT_MIN)) (PreH13 : (nv >= INT_MIN)) (PreH14 : (((lo + hi ) ÷ 2 ) >= INT_MIN)) (PreH15 : (lo <= hi)) (PreH16 : (ec = ((2 * nv ) - 2 ))) (PreH17 : (1 <= lo)) (PreH18 : (lo <= (nv + 1 ))) (PreH19 : (0 <= hi)) (PreH20 : (hi <= nv)) (PreH21 : (1 <= ans)) (PreH22 : (ans <= nv)) (PreH23 : ((Zlength (head_data)) = nv)) (PreH24 : ((Zlength (parent_data)) = nv)) (PreH25 : ((Zlength (order_data)) = nv)) (PreH26 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH27 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH28 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH29 : (Pre nv kv edges )) (PreH30 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH31 : (RootedOrderModel nv edges parent_data order_data )) (PreH32 : (SearchState nv kv edges lo hi ans )),
  ((( &( "mid" ) )) # Int  |-> ((lo + hi ) ÷ 2 ))
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
.

Definition solver_partial_solve_wit_29_aux :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (ans: Z) (hi: Z) (lo: Z) (ec: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (lo <= hi)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= lo)) (PreH4 : (lo <= (nv + 1 ))) (PreH5 : (0 <= hi)) (PreH6 : (hi <= nv)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv)))) (PreH15 : (Pre nv kv edges )) (PreH16 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH17 : (RootedOrderModel nv edges parent_data order_data )) (PreH18 : (SearchState nv kv edges lo hi ans )),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (parent_data)) = nv) ”
  &&  “ ((Zlength (order_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < nv)) -> ((((0 <= (Znth j order_data 0)) /\ ((Znth j order_data 0) < nv)) /\ ((-1) <= (Znth j parent_data 0))) /\ ((Znth j parent_data 0) < nv))) ”
  &&  “ (nv <= 100000) ”
  &&  “ (kv < nv) ”
  &&  “ (1 <= kv) ”
  &&  “ (((lo + hi ) ÷ 2 ) <= nv) ”
  &&  “ (1 <= ((lo + hi ) ÷ 2 )) ”
  &&  “ (lo <= hi) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= lo) ”
  &&  “ (lo <= (nv + 1 )) ”
  &&  “ (0 <= hi) ”
  &&  “ (hi <= nv) ”
  &&  “ (1 <= ans) ”
  &&  “ (ans <= nv) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (parent_data)) = nv) ”
  &&  “ ((Zlength (order_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < nv)) -> ((((0 <= (Znth j_2 order_data 0)) /\ ((Znth j_2 order_data 0) < nv)) /\ ((-1) <= (Znth j_2 parent_data 0))) /\ ((Znth j_2 parent_data 0) < nv))) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  “ (RootedOrderModel nv edges parent_data order_data ) ”
  &&  “ (SearchState nv kv edges lo hi ans ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
.

Definition solver_partial_solve_wit_29 := solver_partial_solve_wit_29_pure -> solver_partial_solve_wit_29_aux.

Definition solver_partial_solve_wit_30_pure :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (Spec nv kv edges ans )) (PreH2 : (Pre nv kv edges )) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= lo)) (PreH5 : (lo <= (nv + 1 ))) (PreH6 : (0 <= hi)) (PreH7 : (hi < lo)) (PreH8 : (hi <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (0 <= nv) ”
  &&  “ ((Zlength (head_data)) = nv) ”
.

Definition solver_partial_solve_wit_30_aux :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (Spec nv kv edges ans )) (PreH2 : (Pre nv kv edges )) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= lo)) (PreH5 : (lo <= (nv + 1 ))) (PreH6 : (0 <= hi)) (PreH7 : (hi < lo)) (PreH8 : (hi <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (0 <= nv) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ (Spec nv kv edges ans ) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= lo) ”
  &&  “ (lo <= (nv + 1 )) ”
  &&  “ (0 <= hi) ”
  &&  “ (hi < lo) ”
  &&  “ (hi <= nv) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (parent_data)) = nv) ”
  &&  “ ((Zlength (order_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  (IntArray.full head_p nv head_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
.

Definition solver_partial_solve_wit_30 := solver_partial_solve_wit_30_pure -> solver_partial_solve_wit_30_aux.

Definition solver_partial_solve_wit_31_pure :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (Spec nv kv edges ans )) (PreH2 : (Pre nv kv edges )) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= lo)) (PreH5 : (lo <= (nv + 1 ))) (PreH6 : (0 <= hi)) (PreH7 : (hi < lo)) (PreH8 : (hi <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ (0 <= ((2 * nv ) - 2 )) ”
) \/
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (ec <= INT_MAX)) (PreH4 : (ans <= INT_MAX)) (PreH5 : (kv <= INT_MAX)) (PreH6 : (nv <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (ec >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (kv >= INT_MIN)) (PreH12 : (nv >= INT_MIN)) (PreH13 : (Spec nv kv edges ans )) (PreH14 : (Pre nv kv edges )) (PreH15 : (ec = ((2 * nv ) - 2 ))) (PreH16 : (1 <= lo)) (PreH17 : (lo <= (nv + 1 ))) (PreH18 : (0 <= hi)) (PreH19 : (hi < lo)) (PreH20 : (hi <= nv)) (PreH21 : ((Zlength (head_data)) = nv)) (PreH22 : ((Zlength (parent_data)) = nv)) (PreH23 : ((Zlength (order_data)) = nv)) (PreH24 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH25 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (0 <= ((2 * nv ) - 2 )) ”
).

Definition solver_partial_solve_wit_31_pure_split_goal_1 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (ec <= INT_MAX)) (PreH4 : (ans <= INT_MAX)) (PreH5 : (kv <= INT_MAX)) (PreH6 : (nv <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (ec >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (kv >= INT_MIN)) (PreH12 : (nv >= INT_MIN)) (PreH13 : (Spec nv kv edges ans )) (PreH14 : (Pre nv kv edges )) (PreH15 : (ec = ((2 * nv ) - 2 ))) (PreH16 : (1 <= lo)) (PreH17 : (lo <= (nv + 1 ))) (PreH18 : (0 <= hi)) (PreH19 : (hi < lo)) (PreH20 : (hi <= nv)) (PreH21 : ((Zlength (head_data)) = nv)) (PreH22 : ((Zlength (parent_data)) = nv)) (PreH23 : ((Zlength (order_data)) = nv)) (PreH24 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH25 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (0 <= ((2 * nv ) - 2 )) ”
.

Definition solver_partial_solve_wit_31_aux :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (Spec nv kv edges ans )) (PreH2 : (Pre nv kv edges )) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= lo)) (PreH5 : (lo <= (nv + 1 ))) (PreH6 : (0 <= hi)) (PreH7 : (hi < lo)) (PreH8 : (hi <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ (0 <= ((2 * nv ) - 2 )) ”
  &&  “ (Spec nv kv edges ans ) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= lo) ”
  &&  “ (lo <= (nv + 1 )) ”
  &&  “ (0 <= hi) ”
  &&  “ (hi < lo) ”
  &&  “ (hi <= nv) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (parent_data)) = nv) ”
  &&  “ ((Zlength (order_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
.

Definition solver_partial_solve_wit_31 := solver_partial_solve_wit_31_pure -> solver_partial_solve_wit_31_aux.

Definition solver_partial_solve_wit_32_pure :=
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (Spec nv kv edges ans )) (PreH2 : (Pre nv kv edges )) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= lo)) (PreH5 : (lo <= (nv + 1 ))) (PreH6 : (0 <= hi)) (PreH7 : (hi < lo)) (PreH8 : (hi <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ (0 <= ((2 * nv ) - 2 )) ”
) \/
(
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (ec <= INT_MAX)) (PreH4 : (ans <= INT_MAX)) (PreH5 : (kv <= INT_MAX)) (PreH6 : (nv <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (ec >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (kv >= INT_MIN)) (PreH12 : (nv >= INT_MIN)) (PreH13 : (Spec nv kv edges ans )) (PreH14 : (Pre nv kv edges )) (PreH15 : (ec = ((2 * nv ) - 2 ))) (PreH16 : (1 <= lo)) (PreH17 : (lo <= (nv + 1 ))) (PreH18 : (0 <= hi)) (PreH19 : (hi < lo)) (PreH20 : (hi <= nv)) (PreH21 : ((Zlength (head_data)) = nv)) (PreH22 : ((Zlength (parent_data)) = nv)) (PreH23 : ((Zlength (order_data)) = nv)) (PreH24 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH25 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (0 <= ((2 * nv ) - 2 )) ”
).

Definition solver_partial_solve_wit_32_pure_split_goal_1 :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (hi <= INT_MAX)) (PreH2 : (lo <= INT_MAX)) (PreH3 : (ec <= INT_MAX)) (PreH4 : (ans <= INT_MAX)) (PreH5 : (kv <= INT_MAX)) (PreH6 : (nv <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (ec >= INT_MIN)) (PreH10 : (ans >= INT_MIN)) (PreH11 : (kv >= INT_MIN)) (PreH12 : (nv >= INT_MIN)) (PreH13 : (Spec nv kv edges ans )) (PreH14 : (Pre nv kv edges )) (PreH15 : (ec = ((2 * nv ) - 2 ))) (PreH16 : (1 <= lo)) (PreH17 : (lo <= (nv + 1 ))) (PreH18 : (0 <= hi)) (PreH19 : (hi < lo)) (PreH20 : (hi <= nv)) (PreH21 : ((Zlength (head_data)) = nv)) (PreH22 : ((Zlength (parent_data)) = nv)) (PreH23 : ((Zlength (order_data)) = nv)) (PreH24 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH25 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (0 <= ((2 * nv ) - 2 )) ”
.

Definition solver_partial_solve_wit_32_aux :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (Spec nv kv edges ans )) (PreH2 : (Pre nv kv edges )) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= lo)) (PreH5 : (lo <= (nv + 1 ))) (PreH6 : (0 <= hi)) (PreH7 : (hi < lo)) (PreH8 : (hi <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  “ (0 <= ((2 * nv ) - 2 )) ”
  &&  “ (Spec nv kv edges ans ) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= lo) ”
  &&  “ (lo <= (nv + 1 )) ”
  &&  “ (0 <= hi) ”
  &&  “ (hi < lo) ”
  &&  “ (hi <= nv) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (parent_data)) = nv) ”
  &&  “ ((Zlength (order_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
.

Definition solver_partial_solve_wit_32 := solver_partial_solve_wit_32_pure -> solver_partial_solve_wit_32_aux.

Definition solver_partial_solve_wit_33_pure :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (Spec nv kv edges ans )) (PreH2 : (Pre nv kv edges )) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= lo)) (PreH5 : (lo <= (nv + 1 ))) (PreH6 : (0 <= hi)) (PreH7 : (hi < lo)) (PreH8 : (hi <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (0 <= nv) ”
  &&  “ ((Zlength (parent_data)) = nv) ”
.

Definition solver_partial_solve_wit_33_aux :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (Spec nv kv edges ans )) (PreH2 : (Pre nv kv edges )) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= lo)) (PreH5 : (lo <= (nv + 1 ))) (PreH6 : (0 <= hi)) (PreH7 : (hi < lo)) (PreH8 : (hi <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (0 <= nv) ”
  &&  “ ((Zlength (parent_data)) = nv) ”
  &&  “ (Spec nv kv edges ans ) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= lo) ”
  &&  “ (lo <= (nv + 1 )) ”
  &&  “ (0 <= hi) ”
  &&  “ (hi < lo) ”
  &&  “ (hi <= nv) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (parent_data)) = nv) ”
  &&  “ ((Zlength (order_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  (IntArray.full parent_p nv parent_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
.

Definition solver_partial_solve_wit_33 := solver_partial_solve_wit_33_pure -> solver_partial_solve_wit_33_aux.

Definition solver_partial_solve_wit_34_pure :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (Spec nv kv edges ans )) (PreH2 : (Pre nv kv edges )) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= lo)) (PreH5 : (lo <= (nv + 1 ))) (PreH6 : (0 <= hi)) (PreH7 : (hi < lo)) (PreH8 : (hi <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (0 <= nv) ”
  &&  “ ((Zlength (order_data)) = nv) ”
.

Definition solver_partial_solve_wit_34_aux :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (Spec nv kv edges ans )) (PreH2 : (Pre nv kv edges )) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= lo)) (PreH5 : (lo <= (nv + 1 ))) (PreH6 : (0 <= hi)) (PreH7 : (hi < lo)) (PreH8 : (hi <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.full order_p nv order_data )
  **  (IntArray.undef_full size_p nv )
|--
  “ (0 <= nv) ”
  &&  “ ((Zlength (order_data)) = nv) ”
  &&  “ (Spec nv kv edges ans ) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= lo) ”
  &&  “ (lo <= (nv + 1 )) ”
  &&  “ (0 <= hi) ”
  &&  “ (hi < lo) ”
  &&  “ (hi <= nv) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (parent_data)) = nv) ”
  &&  “ ((Zlength (order_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  (IntArray.full order_p nv order_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.undef_full size_p nv )
.

Definition solver_partial_solve_wit_34 := solver_partial_solve_wit_34_pure -> solver_partial_solve_wit_34_aux.

Definition solver_partial_solve_wit_35_pure :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (Spec nv kv edges ans )) (PreH2 : (Pre nv kv edges )) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= lo)) (PreH5 : (lo <= (nv + 1 ))) (PreH6 : (0 <= hi)) (PreH7 : (hi < lo)) (PreH8 : (hi <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "kk" ) )) # Int  |-> kv)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "top" ) )) # Int  |-> nv)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.undef_full size_p nv )
|--
  “ (0 <= nv) ”
.

Definition solver_partial_solve_wit_35_aux :=
forall (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (kv: Z) (nv: Z) (eu_pre: Z) (ev_pre: Z) (head_p: Z) (to_p: Z) (next_p: Z) (parent_p: Z) (order_p: Z) (size_p: Z) (ans: Z) (ec: Z) (lo: Z) (hi: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (parent_data: (@list Z)) (order_data: (@list Z)) (PreH1 : (Spec nv kv edges ans )) (PreH2 : (Pre nv kv edges )) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= lo)) (PreH5 : (lo <= (nv + 1 ))) (PreH6 : (0 <= hi)) (PreH7 : (hi < lo)) (PreH8 : (hi <= nv)) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (parent_data)) = nv)) (PreH11 : ((Zlength (order_data)) = nv)) (PreH12 : ((Zlength (to_data)) = ((2 * nv ) - 2 ))) (PreH13 : ((Zlength (next_data)) = ((2 * nv ) - 2 ))),
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
  **  (IntArray.undef_full size_p nv )
|--
  “ (0 <= nv) ”
  &&  “ (Spec nv kv edges ans ) ”
  &&  “ (Pre nv kv edges ) ”
  &&  “ (ec = ((2 * nv ) - 2 )) ”
  &&  “ (1 <= lo) ”
  &&  “ (lo <= (nv + 1 )) ”
  &&  “ (0 <= hi) ”
  &&  “ (hi < lo) ”
  &&  “ (hi <= nv) ”
  &&  “ ((Zlength (head_data)) = nv) ”
  &&  “ ((Zlength (parent_data)) = nv) ”
  &&  “ ((Zlength (order_data)) = nv) ”
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
  &&  (IntArray.undef_full size_p nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "k" ) )) # Int  |-> kv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "next_edge" ) )) # Ptr  |-> next_p)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_p)
  **  ((( &( "order" ) )) # Ptr  |-> order_p)
  **  ((( &( "size_sub" ) )) # Ptr  |-> size_p)
.

Definition solver_partial_solve_wit_35 := solver_partial_solve_wit_35_pure -> solver_partial_solve_wit_35_aux.

Module Type VC_Correct.


Axiom proof_of_feasible_safety_wit_1 : feasible_safety_wit_1.
Axiom proof_of_feasible_safety_wit_2 : feasible_safety_wit_2.
Axiom proof_of_feasible_safety_wit_3 : feasible_safety_wit_3.
Axiom proof_of_feasible_safety_wit_4 : feasible_safety_wit_4.
Axiom proof_of_feasible_safety_wit_5 : feasible_safety_wit_5.
Axiom proof_of_feasible_safety_wit_6 : feasible_safety_wit_6.
Axiom proof_of_feasible_safety_wit_7 : feasible_safety_wit_7.
Axiom proof_of_feasible_safety_wit_8 : feasible_safety_wit_8.
Axiom proof_of_feasible_safety_wit_9 : feasible_safety_wit_9.
Axiom proof_of_feasible_safety_wit_10 : feasible_safety_wit_10.
Axiom proof_of_feasible_safety_wit_11 : feasible_safety_wit_11.
Axiom proof_of_feasible_safety_wit_12 : feasible_safety_wit_12.
Axiom proof_of_feasible_safety_wit_13 : feasible_safety_wit_13.
Axiom proof_of_feasible_safety_wit_14 : feasible_safety_wit_14.
Axiom proof_of_feasible_safety_wit_15 : feasible_safety_wit_15.
Axiom proof_of_feasible_safety_wit_16 : feasible_safety_wit_16.
Axiom proof_of_feasible_safety_wit_17 : feasible_safety_wit_17.
Axiom proof_of_feasible_safety_wit_18 : feasible_safety_wit_18.
Axiom proof_of_feasible_safety_wit_19 : feasible_safety_wit_19.
Axiom proof_of_feasible_entail_wit_1 : feasible_entail_wit_1.
Axiom proof_of_feasible_entail_wit_2 : feasible_entail_wit_2.
Axiom proof_of_feasible_entail_wit_3 : feasible_entail_wit_3.
Axiom proof_of_feasible_entail_wit_4_1 : feasible_entail_wit_4_1.
Axiom proof_of_feasible_entail_wit_4_2 : feasible_entail_wit_4_2.
Axiom proof_of_feasible_entail_wit_4_3 : feasible_entail_wit_4_3.
Axiom proof_of_feasible_entail_wit_4_4 : feasible_entail_wit_4_4.
Axiom proof_of_feasible_return_wit_1 : feasible_return_wit_1.
Axiom proof_of_feasible_return_wit_2 : feasible_return_wit_2.
Axiom proof_of_feasible_partial_solve_wit_1 : feasible_partial_solve_wit_1.
Axiom proof_of_feasible_partial_solve_wit_2 : feasible_partial_solve_wit_2.
Axiom proof_of_feasible_partial_solve_wit_3 : feasible_partial_solve_wit_3.
Axiom proof_of_feasible_partial_solve_wit_4 : feasible_partial_solve_wit_4.
Axiom proof_of_feasible_partial_solve_wit_5 : feasible_partial_solve_wit_5.
Axiom proof_of_feasible_partial_solve_wit_6 : feasible_partial_solve_wit_6.
Axiom proof_of_feasible_partial_solve_wit_7 : feasible_partial_solve_wit_7.
Axiom proof_of_feasible_partial_solve_wit_8 : feasible_partial_solve_wit_8.
Axiom proof_of_feasible_partial_solve_wit_9 : feasible_partial_solve_wit_9.
Axiom proof_of_feasible_partial_solve_wit_10 : feasible_partial_solve_wit_10.
Axiom proof_of_feasible_partial_solve_wit_11 : feasible_partial_solve_wit_11.
Axiom proof_of_feasible_partial_solve_wit_12 : feasible_partial_solve_wit_12.
Axiom proof_of_feasible_partial_solve_wit_13 : feasible_partial_solve_wit_13.
Axiom proof_of_feasible_partial_solve_wit_14 : feasible_partial_solve_wit_14.
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
Axiom proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Axiom proof_of_solver_safety_wit_29 : solver_safety_wit_29.
Axiom proof_of_solver_safety_wit_30 : solver_safety_wit_30.
Axiom proof_of_solver_safety_wit_31 : solver_safety_wit_31.
Axiom proof_of_solver_safety_wit_32 : solver_safety_wit_32.
Axiom proof_of_solver_safety_wit_33 : solver_safety_wit_33.
Axiom proof_of_solver_safety_wit_34 : solver_safety_wit_34.
Axiom proof_of_solver_safety_wit_35 : solver_safety_wit_35.
Axiom proof_of_solver_safety_wit_36 : solver_safety_wit_36.
Axiom proof_of_solver_safety_wit_37 : solver_safety_wit_37.
Axiom proof_of_solver_safety_wit_38 : solver_safety_wit_38.
Axiom proof_of_solver_safety_wit_39 : solver_safety_wit_39.
Axiom proof_of_solver_safety_wit_40 : solver_safety_wit_40.
Axiom proof_of_solver_safety_wit_41 : solver_safety_wit_41.
Axiom proof_of_solver_safety_wit_42 : solver_safety_wit_42.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Axiom proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Axiom proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Axiom proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Axiom proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Axiom proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Axiom proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.
Axiom proof_of_solver_partial_solve_wit_15_pure : solver_partial_solve_wit_15_pure.
Axiom proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15.
Axiom proof_of_solver_partial_solve_wit_16_pure : solver_partial_solve_wit_16_pure.
Axiom proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16.
Axiom proof_of_solver_partial_solve_wit_17_pure : solver_partial_solve_wit_17_pure.
Axiom proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17.
Axiom proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18.
Axiom proof_of_solver_partial_solve_wit_19 : solver_partial_solve_wit_19.
Axiom proof_of_solver_partial_solve_wit_20 : solver_partial_solve_wit_20.
Axiom proof_of_solver_partial_solve_wit_21 : solver_partial_solve_wit_21.
Axiom proof_of_solver_partial_solve_wit_22 : solver_partial_solve_wit_22.
Axiom proof_of_solver_partial_solve_wit_23 : solver_partial_solve_wit_23.
Axiom proof_of_solver_partial_solve_wit_24 : solver_partial_solve_wit_24.
Axiom proof_of_solver_partial_solve_wit_25 : solver_partial_solve_wit_25.
Axiom proof_of_solver_partial_solve_wit_26 : solver_partial_solve_wit_26.
Axiom proof_of_solver_partial_solve_wit_27 : solver_partial_solve_wit_27.
Axiom proof_of_solver_partial_solve_wit_28 : solver_partial_solve_wit_28.
Axiom proof_of_solver_partial_solve_wit_29_pure : solver_partial_solve_wit_29_pure.
Axiom proof_of_solver_partial_solve_wit_29 : solver_partial_solve_wit_29.
Axiom proof_of_solver_partial_solve_wit_30_pure : solver_partial_solve_wit_30_pure.
Axiom proof_of_solver_partial_solve_wit_30 : solver_partial_solve_wit_30.
Axiom proof_of_solver_partial_solve_wit_31_pure : solver_partial_solve_wit_31_pure.
Axiom proof_of_solver_partial_solve_wit_31 : solver_partial_solve_wit_31.
Axiom proof_of_solver_partial_solve_wit_32_pure : solver_partial_solve_wit_32_pure.
Axiom proof_of_solver_partial_solve_wit_32 : solver_partial_solve_wit_32.
Axiom proof_of_solver_partial_solve_wit_33_pure : solver_partial_solve_wit_33_pure.
Axiom proof_of_solver_partial_solve_wit_33 : solver_partial_solve_wit_33.
Axiom proof_of_solver_partial_solve_wit_34_pure : solver_partial_solve_wit_34_pure.
Axiom proof_of_solver_partial_solve_wit_34 : solver_partial_solve_wit_34.
Axiom proof_of_solver_partial_solve_wit_35_pure : solver_partial_solve_wit_35_pure.
Axiom proof_of_solver_partial_solve_wit_35 : solver_partial_solve_wit_35.

End VC_Correct.
