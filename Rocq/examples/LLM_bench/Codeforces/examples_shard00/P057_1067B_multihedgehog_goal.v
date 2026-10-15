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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P057_1067B_multihedgehog_lib.
Local Open Scope sac.

(*----- Function bfs -----*)

Definition bfs_safety_wit_1 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) ,
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "l" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval nv_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> retval)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.full_shape parent_pre nv_bfs_run )
  **  (IntArray.full_shape dist_pre nv_bfs_run )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bfs_safety_wit_2 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) ,
  ((( &( "l" ) )) # Int  |->_)
  **  (IntArray.undef_full retval nv_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> retval)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.full_shape parent_pre nv_bfs_run )
  **  (IntArray.full_shape dist_pre nv_bfs_run )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bfs_safety_wit_3 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) ,
  (((retval + (0 * sizeof(INT)))) # Int  |-> src_pre)
  **  (IntArray.undef_seg retval 1 nv_bfs_run )
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "l" ) )) # Int  |-> 0)
  **  ((( &( "q" ) )) # Ptr  |-> retval)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.full_shape parent_pre nv_bfs_run )
  **  (IntArray.full_shape dist_pre nv_bfs_run )
|--
  “ ((0 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 + 1 )) ”
.

Definition bfs_safety_wit_4 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (((retval + (0 * sizeof(INT)))) # Int  |-> src_pre)
  **  (IntArray.undef_seg retval 1 nv_bfs_run )
  **  ((( &( "r" ) )) # Int  |-> (0 + 1 ))
  **  ((( &( "l" ) )) # Int  |-> 0)
  **  ((( &( "q" ) )) # Ptr  |-> retval)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.full_shape parent_pre nv_bfs_run )
  **  (IntArray.full_shape dist_pre nv_bfs_run )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bfs_safety_wit_5 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (dist_data: (@list Z)) (parent_data: (@list Z)) (i: Z) (r: Z) (l: Z) (PreH1 : (i < nv_bfs_run)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH8 : (l = 0)) (PreH9 : (r = 1)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv_bfs_run)) (PreH12 : ((Zlength (parent_data)) = nv_bfs_run)) (PreH13 : ((Zlength (dist_data)) = nv_bfs_run)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data 0) = (-1)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data 0) = (-1)))) ,
  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (IntArray.seg q 0 1 (cons (src_pre) ((@nil Z))) )
  **  (IntArray.undef_seg q 1 nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition bfs_safety_wit_6 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (dist_data: (@list Z)) (parent_data: (@list Z)) (i: Z) (r: Z) (l: Z) (PreH1 : (i < nv_bfs_run)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH8 : (l = 0)) (PreH9 : (r = 1)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv_bfs_run)) (PreH12 : ((Zlength (parent_data)) = nv_bfs_run)) (PreH13 : ((Zlength (dist_data)) = nv_bfs_run)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data 0) = (-1)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data 0) = (-1)))) ,
  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (IntArray.seg q 0 1 (cons (src_pre) ((@nil Z))) )
  **  (IntArray.undef_seg q 1 nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bfs_safety_wit_7 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (dist_data: (@list Z)) (parent_data: (@list Z)) (i: Z) (r: Z) (l: Z) (PreH1 : (i < nv_bfs_run)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH8 : (l = 0)) (PreH9 : (r = 1)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv_bfs_run)) (PreH12 : ((Zlength (parent_data)) = nv_bfs_run)) (PreH13 : ((Zlength (dist_data)) = nv_bfs_run)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data 0) = (-1)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data 0) = (-1)))) ,
  (IntArray.full dist_pre nv_bfs_run (replace_Znth (i) ((-1)) (dist_data)) )
  **  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (IntArray.seg q 0 1 (cons (src_pre) ((@nil Z))) )
  **  (IntArray.undef_seg q 1 nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition bfs_safety_wit_8 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (dist_data: (@list Z)) (parent_data: (@list Z)) (i: Z) (r: Z) (l: Z) (PreH1 : (i < nv_bfs_run)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH8 : (l = 0)) (PreH9 : (r = 1)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv_bfs_run)) (PreH12 : ((Zlength (parent_data)) = nv_bfs_run)) (PreH13 : ((Zlength (dist_data)) = nv_bfs_run)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data 0) = (-1)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data 0) = (-1)))) ,
  (IntArray.full dist_pre nv_bfs_run (replace_Znth (i) ((-1)) (dist_data)) )
  **  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (IntArray.seg q 0 1 (cons (src_pre) ((@nil Z))) )
  **  (IntArray.undef_seg q 1 nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bfs_safety_wit_9 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (dist_data: (@list Z)) (parent_data: (@list Z)) (i: Z) (r: Z) (l: Z) (PreH1 : (i < nv_bfs_run)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH8 : (l = 0)) (PreH9 : (r = 1)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv_bfs_run)) (PreH12 : ((Zlength (parent_data)) = nv_bfs_run)) (PreH13 : ((Zlength (dist_data)) = nv_bfs_run)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data 0) = (-1)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data 0) = (-1)))) ,
  (IntArray.full parent_pre nv_bfs_run (replace_Znth (i) ((-1)) (parent_data)) )
  **  (IntArray.full dist_pre nv_bfs_run (replace_Znth (i) ((-1)) (dist_data)) )
  **  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (IntArray.seg q 0 1 (cons (src_pre) ((@nil Z))) )
  **  (IntArray.undef_seg q 1 nv_bfs_run )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition bfs_safety_wit_10 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (dist_data: (@list Z)) (parent_data: (@list Z)) (i: Z) (r: Z) (l: Z) (PreH1 : (i >= nv_bfs_run)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH8 : (l = 0)) (PreH9 : (r = 1)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv_bfs_run)) (PreH12 : ((Zlength (parent_data)) = nv_bfs_run)) (PreH13 : ((Zlength (dist_data)) = nv_bfs_run)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data 0) = (-1)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data 0) = (-1)))) ,
  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (IntArray.seg q 0 1 (cons (src_pre) ((@nil Z))) )
  **  (IntArray.undef_seg q 1 nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bfs_safety_wit_11 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : (l < r)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH5 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH6 : (0 <= l)) (PreH7 : (l <= r)) (PreH8 : (r = (Zlength (queue_data)))) (PreH9 : (r <= nv_bfs_run)) (PreH10 : (0 <= far)) (PreH11 : (far < nv_bfs_run)) (PreH12 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH13 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data )) ,
  (IntArray.seg q 0 r queue_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth (l - 0 ) queue_data 0))
  **  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "far" ) )) # Int  |-> far)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
|--
  “ ((l + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (l + 1 )) ”
.

Definition bfs_safety_wit_12 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : (1 <= nv_bfs_run)) (PreH2 : (nv_bfs_run <= 100000)) (PreH3 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH4 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH5 : (0 < l)) (PreH6 : (l <= r)) (PreH7 : (r = (Zlength (queue_data)))) (PreH8 : (r <= nv_bfs_run)) (PreH9 : (0 <= v)) (PreH10 : (v < nv_bfs_run)) (PreH11 : (0 <= far)) (PreH12 : (far < nv_bfs_run)) (PreH13 : ((-1) <= e)) (PreH14 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH15 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH16 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH17 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "far" ) )) # Int  |-> far)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition bfs_safety_wit_13 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : (1 <= nv_bfs_run)) (PreH2 : (nv_bfs_run <= 100000)) (PreH3 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH4 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH5 : (0 < l)) (PreH6 : (l <= r)) (PreH7 : (r = (Zlength (queue_data)))) (PreH8 : (r <= nv_bfs_run)) (PreH9 : (0 <= v)) (PreH10 : (v < nv_bfs_run)) (PreH11 : (0 <= far)) (PreH12 : (far < nv_bfs_run)) (PreH13 : ((-1) <= e)) (PreH14 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH15 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH16 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH17 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "far" ) )) # Int  |-> far)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bfs_safety_wit_14 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : (e <> (-1))) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH5 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH6 : (0 < l)) (PreH7 : (l <= r)) (PreH8 : (r = (Zlength (queue_data)))) (PreH9 : (r <= nv_bfs_run)) (PreH10 : (0 <= v)) (PreH11 : (v < nv_bfs_run)) (PreH12 : (0 <= far)) (PreH13 : (far < nv_bfs_run)) (PreH14 : ((-1) <= e)) (PreH15 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH16 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH17 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH18 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.full dist_pre nv_bfs_run dist_data )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "far" ) )) # Int  |-> far)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bfs_safety_wit_15 := 
(
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.full dist_pre nv_bfs_run dist_data )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "far" ) )) # Int  |-> far)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
|--
  “ (((Znth v dist_data 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth v dist_data 0) + 1 )) ”
) \/
(
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.full dist_pre nv_bfs_run dist_data )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "far" ) )) # Int  |-> far)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
|--
  “ (((Znth v dist_data 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth v dist_data 0) + 1 )) ”
).

Definition bfs_safety_wit_15_split_goal_1 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.full dist_pre nv_bfs_run dist_data )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "far" ) )) # Int  |-> far)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
|--
  “ (((Znth v dist_data 0) + 1 ) <= INT_MAX) ”
.

Definition bfs_safety_wit_15_split_goal_2 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.full dist_pre nv_bfs_run dist_data )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "far" ) )) # Int  |-> far)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
|--
  “ ((INT_MIN) <= ((Znth v dist_data 0) + 1 )) ”
.

Definition bfs_safety_wit_16 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.full dist_pre nv_bfs_run dist_data )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "far" ) )) # Int  |-> far)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bfs_safety_wit_17 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.seg q 0 (r + 1 ) (app (queue_data) ((cons ((Znth e to_data_bfs_run 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg q (r + 1 ) nv_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (v) (parent_data)) )
  **  (IntArray.full dist_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (((Znth v dist_data 0) + 1 )) (dist_data)) )
  **  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "far" ) )) # Int  |-> far)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> q)
|--
  “ ((r + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition bfs_entail_wit_1 := 
(
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) ,
  (((retval + (0 * sizeof(INT)))) # Int  |-> src_pre)
  **  (IntArray.undef_seg retval 1 nv_bfs_run )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.full_shape parent_pre nv_bfs_run )
  **  (IntArray.full_shape dist_pre nv_bfs_run )
|--
  EX (dist_data: (@list Z))  (parent_data: (@list Z)) ,
  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (0 <= src_pre) ” 
  &&  “ (src_pre < nv_bfs_run) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((0 + 1 ) = 1) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= nv_bfs_run) ” 
  &&  “ ((Zlength (parent_data)) = nv_bfs_run) ” 
  &&  “ ((Zlength (dist_data)) = nv_bfs_run) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < 0)) -> ((Znth j parent_data 0) = (-1))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < 0)) -> ((Znth j_2 dist_data 0) = (-1))) ”
  &&  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg retval 0 1 (cons (src_pre) ((@nil Z))) )
  **  (IntArray.undef_seg retval 1 nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
) \/
(
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (retval: Z) (PreH1 : (src_pre <= INT_MAX)) (PreH2 : (src_pre >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= nv_bfs_run)) (PreH5 : (nv_bfs_run <= 100000)) (PreH6 : (0 <= src_pre)) (PreH7 : (src_pre < nv_bfs_run)) (PreH8 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH9 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) ,
  (((retval + (0 * sizeof(INT)))) # Int  |-> src_pre)
  **  (IntArray.full_shape parent_pre nv_bfs_run )
  **  (IntArray.full_shape dist_pre nv_bfs_run )
|--
  EX (dist_data: (@list Z))  (parent_data: (@list Z)) ,
  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (0 <= src_pre) ” 
  &&  “ (src_pre < nv_bfs_run) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ ((0 + 1 ) = 1) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= nv_bfs_run) ” 
  &&  “ ((Zlength (parent_data)) = nv_bfs_run) ” 
  &&  “ ((Zlength (dist_data)) = nv_bfs_run) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < 0)) -> ((Znth j parent_data 0) = (-1))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < 0)) -> ((Znth j_2 dist_data 0) = (-1))) ”
  &&  (IntArray.seg retval 0 1 (cons (src_pre) ((@nil Z))) )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
).

Definition bfs_entail_wit_2 := 
(
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (dist_data_2: (@list Z)) (parent_data_2: (@list Z)) (i: Z) (r: Z) (l: Z) (PreH1 : (i < nv_bfs_run)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH8 : (l = 0)) (PreH9 : (r = 1)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv_bfs_run)) (PreH12 : ((Zlength (parent_data_2)) = nv_bfs_run)) (PreH13 : ((Zlength (dist_data_2)) = nv_bfs_run)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data_2 0) = (-1)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data_2 0) = (-1)))) ,
  (IntArray.full parent_pre nv_bfs_run (replace_Znth (i) ((-1)) (parent_data_2)) )
  **  (IntArray.full dist_pre nv_bfs_run (replace_Znth (i) ((-1)) (dist_data_2)) )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 1 (cons (src_pre) ((@nil Z))) )
  **  (IntArray.undef_seg q 1 nv_bfs_run )
|--
  EX (dist_data: (@list Z))  (parent_data: (@list Z)) ,
  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (0 <= src_pre) ” 
  &&  “ (src_pre < nv_bfs_run) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (l = 0) ” 
  &&  “ (r = 1) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nv_bfs_run) ” 
  &&  “ ((Zlength (parent_data)) = nv_bfs_run) ” 
  &&  “ ((Zlength (dist_data)) = nv_bfs_run) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (i + 1 ))) -> ((Znth j parent_data 0) = (-1))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (i + 1 ))) -> ((Znth j_2 dist_data 0) = (-1))) ”
  &&  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 1 (cons (src_pre) ((@nil Z))) )
  **  (IntArray.undef_seg q 1 nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
) \/
(
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (dist_data_2: (@list Z)) (parent_data_2: (@list Z)) (i: Z) (r: Z) (l: Z) (PreH1 : (i < nv_bfs_run)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH8 : (l = 0)) (PreH9 : (r = 1)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv_bfs_run)) (PreH12 : ((Zlength (parent_data_2)) = nv_bfs_run)) (PreH13 : ((Zlength (dist_data_2)) = nv_bfs_run)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data_2 0) = (-1)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data_2 0) = (-1)))) ,
  TT && emp 
|--
  “ ((Zlength ((replace_Znth (i) ((-1)) (dist_data_2)))) = nv_bfs_run) ” 
  &&  “ ((Zlength ((replace_Znth (i) ((-1)) (parent_data_2)))) = nv_bfs_run) ”
  &&  emp
).

Definition bfs_entail_wit_2_split_goal_1 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (dist_data_2: (@list Z)) (parent_data_2: (@list Z)) (i: Z) (r: Z) (l: Z) (PreH1 : (i < nv_bfs_run)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH8 : (l = 0)) (PreH9 : (r = 1)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv_bfs_run)) (PreH12 : ((Zlength (parent_data_2)) = nv_bfs_run)) (PreH13 : ((Zlength (dist_data_2)) = nv_bfs_run)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data_2 0) = (-1)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data_2 0) = (-1)))) ,
  ((Zlength ((replace_Znth (i) ((-1)) (dist_data_2)))) = nv_bfs_run)
.

Definition bfs_entail_wit_2_split_goal_2 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (dist_data_2: (@list Z)) (parent_data_2: (@list Z)) (i: Z) (r: Z) (l: Z) (PreH1 : (i < nv_bfs_run)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH8 : (l = 0)) (PreH9 : (r = 1)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv_bfs_run)) (PreH12 : ((Zlength (parent_data_2)) = nv_bfs_run)) (PreH13 : ((Zlength (dist_data_2)) = nv_bfs_run)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data_2 0) = (-1)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data_2 0) = (-1)))) ,
  ((Zlength ((replace_Znth (i) ((-1)) (parent_data_2)))) = nv_bfs_run)
.

Definition bfs_entail_wit_3 := 
(
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (dist_data_2: (@list Z)) (parent_data_2: (@list Z)) (i: Z) (r: Z) (l: Z) (PreH1 : (i >= nv_bfs_run)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH8 : (l = 0)) (PreH9 : (r = 1)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv_bfs_run)) (PreH12 : ((Zlength (parent_data_2)) = nv_bfs_run)) (PreH13 : ((Zlength (dist_data_2)) = nv_bfs_run)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data_2 0) = (-1)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data_2 0) = (-1)))) ,
  (IntArray.full dist_pre nv_bfs_run (replace_Znth (src_pre) (0) (dist_data_2)) )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 1 (cons (src_pre) ((@nil Z))) )
  **  (IntArray.undef_seg q 1 nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data_2 )
|--
  EX (parent_data: (@list Z))  (dist_data: (@list Z))  (queue_data: (@list Z)) ,
  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 <= l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= src_pre) ” 
  &&  “ (src_pre < nv_bfs_run) ” 
  &&  “ forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run))) ” 
  &&  “ (BFSQueueState nv_bfs_run edges_bfs_run src_pre l src_pre queue_data parent_data dist_data ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
) \/
(
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (dist_data_2: (@list Z)) (parent_data_2: (@list Z)) (i: Z) (r: Z) (l: Z) (PreH1 : (i >= nv_bfs_run)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH8 : (l = 0)) (PreH9 : (r = 1)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv_bfs_run)) (PreH12 : ((Zlength (parent_data_2)) = nv_bfs_run)) (PreH13 : ((Zlength (dist_data_2)) = nv_bfs_run)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data_2 0) = (-1)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data_2 0) = (-1)))) ,
  TT && emp 
|--
  “ (BFSQueueState nv_bfs_run edges_bfs_run src_pre 0 src_pre (cons (src_pre) ((@nil Z))) parent_data_2 (replace_Znth (src_pre) (0) (dist_data_2)) ) ” 
  &&  “ forall (qindex: Z) , (((0 <= qindex) /\ (qindex < 1)) -> ((0 <= (Znth qindex (cons (src_pre) ((@nil Z))) 0)) /\ ((Znth qindex (cons (src_pre) ((@nil Z))) 0) < (Zlength (parent_data_2))))) ” 
  &&  “ (1 = (Zlength ((cons (src_pre) ((@nil Z)))))) ”
  &&  emp
).

Definition bfs_entail_wit_3_split_goal_1 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (dist_data_2: (@list Z)) (parent_data_2: (@list Z)) (i: Z) (r: Z) (l: Z) (PreH1 : (i >= nv_bfs_run)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH8 : (l = 0)) (PreH9 : (r = 1)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv_bfs_run)) (PreH12 : ((Zlength (parent_data_2)) = nv_bfs_run)) (PreH13 : ((Zlength (dist_data_2)) = nv_bfs_run)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data_2 0) = (-1)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data_2 0) = (-1)))) ,
  (BFSQueueState nv_bfs_run edges_bfs_run src_pre 0 src_pre (cons (src_pre) ((@nil Z))) parent_data_2 (replace_Znth (src_pre) (0) (dist_data_2)) )
.

Definition bfs_entail_wit_3_split_goal_2 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (dist_data_2: (@list Z)) (parent_data_2: (@list Z)) (i: Z) (r: Z) (l: Z) (PreH1 : (i >= nv_bfs_run)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH8 : (l = 0)) (PreH9 : (r = 1)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv_bfs_run)) (PreH12 : ((Zlength (parent_data_2)) = nv_bfs_run)) (PreH13 : ((Zlength (dist_data_2)) = nv_bfs_run)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data_2 0) = (-1)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data_2 0) = (-1)))) ,
  forall (qindex: Z) , (((0 <= qindex) /\ (qindex < 1)) -> ((0 <= (Znth qindex (cons (src_pre) ((@nil Z))) 0)) /\ ((Znth qindex (cons (src_pre) ((@nil Z))) 0) < (Zlength (parent_data_2)))))
.

Definition bfs_entail_wit_3_split_goal_3 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (dist_data_2: (@list Z)) (parent_data_2: (@list Z)) (i: Z) (r: Z) (l: Z) (PreH1 : (i >= nv_bfs_run)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH8 : (l = 0)) (PreH9 : (r = 1)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv_bfs_run)) (PreH12 : ((Zlength (parent_data_2)) = nv_bfs_run)) (PreH13 : ((Zlength (dist_data_2)) = nv_bfs_run)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data_2 0) = (-1)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data_2 0) = (-1)))) ,
  (1 = (Zlength ((cons (src_pre) ((@nil Z))))))
.

Definition bfs_entail_wit_4_1 := 
(
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth (l - 0 ) queue_data 0) dist_data_2 0) > (Znth far dist_data_2 0))) (PreH2 : (l < r)) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 <= l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= far)) (PreH12 : (far < nv_bfs_run)) (PreH13 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH14 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data_2 dist_data_2 )) ,
  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full dist_pre nv_bfs_run dist_data_2 )
  **  (IntArray.seg q 0 r queue_data )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data_2 )
|--
  EX (parent_data: (@list Z))  (dist_data: (@list Z))  (queue_data_2: (@list Z)) ,
  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 < (l + 1 )) ” 
  &&  “ ((l + 1 ) <= r) ” 
  &&  “ (r = (Zlength (queue_data_2))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= (Znth (l - 0 ) queue_data 0)) ” 
  &&  “ ((Znth (l - 0 ) queue_data 0) < nv_bfs_run) ” 
  &&  “ (0 <= (Znth (l - 0 ) queue_data 0)) ” 
  &&  “ ((Znth (l - 0 ) queue_data 0) < nv_bfs_run) ” 
  &&  “ ((-1) <= (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0)) ” 
  &&  “ ((Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )) ” 
  &&  “ (((Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) <> (-1)) -> ((((0 <= (Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) to_data_bfs_run 0)) /\ ((Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) next_data_bfs_run 0))) /\ ((Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ” 
  &&  “ ((((Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) <> (-1)) /\ ((Znth (Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run)) ” 
  &&  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre (l + 1 ) (Znth (l - 0 ) queue_data 0) queue_data_2 parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run (Znth (l - 0 ) queue_data 0) (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data_2 )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
) \/
(
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth (l - 0 ) queue_data 0) dist_data_2 0) > (Znth far dist_data_2 0))) (PreH2 : (l < r)) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 <= l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= far)) (PreH12 : (far < nv_bfs_run)) (PreH13 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH14 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data_2 dist_data_2 )) ,
  TT && emp 
|--
  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre (l + 1 ) (Znth (l - 0 ) queue_data 0) queue_data parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run (Znth (l - 0 ) queue_data 0) (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) ) ” 
  &&  “ ((((Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) <> (-1)) /\ ((Znth (Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run)) ” 
  &&  “ (((Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) <> (-1)) -> ((((0 <= (Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) to_data_bfs_run 0)) /\ ((Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) next_data_bfs_run 0))) /\ ((Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ” 
  &&  “ ((Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )) ” 
  &&  “ ((-1) <= (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0)) ”
  &&  emp
).

Definition bfs_entail_wit_4_1_split_goal_1 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth (l - 0 ) queue_data 0) dist_data_2 0) > (Znth far dist_data_2 0))) (PreH2 : (l < r)) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 <= l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= far)) (PreH12 : (far < nv_bfs_run)) (PreH13 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH14 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data_2 dist_data_2 )) ,
  (BFSAdjState nv_bfs_run edges_bfs_run src_pre (l + 1 ) (Znth (l - 0 ) queue_data 0) queue_data parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run (Znth (l - 0 ) queue_data 0) (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) )
.

Definition bfs_entail_wit_4_1_split_goal_2 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth (l - 0 ) queue_data 0) dist_data_2 0) > (Znth far dist_data_2 0))) (PreH2 : (l < r)) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 <= l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= far)) (PreH12 : (far < nv_bfs_run)) (PreH13 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH14 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data_2 dist_data_2 )) ,
  ((((Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) <> (-1)) /\ ((Znth (Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run))
.

Definition bfs_entail_wit_4_1_split_goal_3 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth (l - 0 ) queue_data 0) dist_data_2 0) > (Znth far dist_data_2 0))) (PreH2 : (l < r)) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 <= l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= far)) (PreH12 : (far < nv_bfs_run)) (PreH13 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH14 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data_2 dist_data_2 )) ,
  (((Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) <> (-1)) -> ((((0 <= (Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) to_data_bfs_run 0)) /\ ((Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) next_data_bfs_run 0))) /\ ((Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))
.

Definition bfs_entail_wit_4_1_split_goal_4 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth (l - 0 ) queue_data 0) dist_data_2 0) > (Znth far dist_data_2 0))) (PreH2 : (l < r)) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 <= l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= far)) (PreH12 : (far < nv_bfs_run)) (PreH13 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH14 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data_2 dist_data_2 )) ,
  ((Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))
.

Definition bfs_entail_wit_4_1_split_goal_5 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth (l - 0 ) queue_data 0) dist_data_2 0) > (Znth far dist_data_2 0))) (PreH2 : (l < r)) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 <= l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= far)) (PreH12 : (far < nv_bfs_run)) (PreH13 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH14 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data_2 dist_data_2 )) ,
  ((-1) <= (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0))
.

Definition bfs_entail_wit_4_2 := 
(
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth (l - 0 ) queue_data 0) dist_data_2 0) <= (Znth far dist_data_2 0))) (PreH2 : (l < r)) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 <= l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= far)) (PreH12 : (far < nv_bfs_run)) (PreH13 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH14 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data_2 dist_data_2 )) ,
  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full dist_pre nv_bfs_run dist_data_2 )
  **  (IntArray.seg q 0 r queue_data )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data_2 )
|--
  EX (parent_data: (@list Z))  (dist_data: (@list Z))  (queue_data_2: (@list Z)) ,
  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 < (l + 1 )) ” 
  &&  “ ((l + 1 ) <= r) ” 
  &&  “ (r = (Zlength (queue_data_2))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= (Znth (l - 0 ) queue_data 0)) ” 
  &&  “ ((Znth (l - 0 ) queue_data 0) < nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ ((-1) <= (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0)) ” 
  &&  “ ((Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )) ” 
  &&  “ (((Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) <> (-1)) -> ((((0 <= (Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) to_data_bfs_run 0)) /\ ((Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) next_data_bfs_run 0))) /\ ((Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ” 
  &&  “ ((((Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) <> (-1)) /\ ((Znth (Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run)) ” 
  &&  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre (l + 1 ) far queue_data_2 parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run (Znth (l - 0 ) queue_data 0) (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data_2 )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
) \/
(
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth (l - 0 ) queue_data 0) dist_data_2 0) <= (Znth far dist_data_2 0))) (PreH2 : (l < r)) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 <= l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= far)) (PreH12 : (far < nv_bfs_run)) (PreH13 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH14 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data_2 dist_data_2 )) ,
  TT && emp 
|--
  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre (l + 1 ) far queue_data parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run (Znth (l - 0 ) queue_data 0) (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) ) ” 
  &&  “ ((((Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) <> (-1)) /\ ((Znth (Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run)) ” 
  &&  “ (((Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) <> (-1)) -> ((((0 <= (Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) to_data_bfs_run 0)) /\ ((Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) next_data_bfs_run 0))) /\ ((Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ” 
  &&  “ ((Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )) ” 
  &&  “ ((-1) <= (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0)) ”
  &&  emp
).

Definition bfs_entail_wit_4_2_split_goal_1 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth (l - 0 ) queue_data 0) dist_data_2 0) <= (Znth far dist_data_2 0))) (PreH2 : (l < r)) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 <= l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= far)) (PreH12 : (far < nv_bfs_run)) (PreH13 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH14 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data_2 dist_data_2 )) ,
  (BFSAdjState nv_bfs_run edges_bfs_run src_pre (l + 1 ) far queue_data parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run (Znth (l - 0 ) queue_data 0) (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) )
.

Definition bfs_entail_wit_4_2_split_goal_2 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth (l - 0 ) queue_data 0) dist_data_2 0) <= (Znth far dist_data_2 0))) (PreH2 : (l < r)) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 <= l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= far)) (PreH12 : (far < nv_bfs_run)) (PreH13 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH14 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data_2 dist_data_2 )) ,
  ((((Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) <> (-1)) /\ ((Znth (Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run))
.

Definition bfs_entail_wit_4_2_split_goal_3 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth (l - 0 ) queue_data 0) dist_data_2 0) <= (Znth far dist_data_2 0))) (PreH2 : (l < r)) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 <= l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= far)) (PreH12 : (far < nv_bfs_run)) (PreH13 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH14 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data_2 dist_data_2 )) ,
  (((Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) <> (-1)) -> ((((0 <= (Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) to_data_bfs_run 0)) /\ ((Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) next_data_bfs_run 0))) /\ ((Znth (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))
.

Definition bfs_entail_wit_4_2_split_goal_4 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth (l - 0 ) queue_data 0) dist_data_2 0) <= (Znth far dist_data_2 0))) (PreH2 : (l < r)) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 <= l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= far)) (PreH12 : (far < nv_bfs_run)) (PreH13 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH14 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data_2 dist_data_2 )) ,
  ((Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))
.

Definition bfs_entail_wit_4_2_split_goal_5 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth (l - 0 ) queue_data 0) dist_data_2 0) <= (Znth far dist_data_2 0))) (PreH2 : (l < r)) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 <= l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= far)) (PreH12 : (far < nv_bfs_run)) (PreH13 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH14 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data_2 dist_data_2 )) ,
  ((-1) <= (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0))
.

Definition bfs_entail_wit_5_1 := 
(
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data_2: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data_2)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 (r + 1 ) (app (queue_data_2) ((cons ((Znth e to_data_bfs_run 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg q (r + 1 ) nv_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (v) (parent_data_2)) )
  **  (IntArray.full dist_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (((Znth v dist_data_2 0) + 1 )) (dist_data_2)) )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
|--
  EX (parent_data: (@list Z))  (dist_data: (@list Z))  (queue_data: (@list Z)) ,
  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 < l) ” 
  &&  “ (l <= (r + 1 )) ” 
  &&  “ ((r + 1 ) = (Zlength (queue_data))) ” 
  &&  “ ((r + 1 ) <= nv_bfs_run) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ ((-1) <= (Znth e next_data_bfs_run 0)) ” 
  &&  “ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )) ” 
  &&  “ (((Znth e next_data_bfs_run 0) <> (-1)) -> ((((0 <= (Znth (Znth e next_data_bfs_run 0) to_data_bfs_run 0)) /\ ((Znth (Znth e next_data_bfs_run 0) to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth (Znth e next_data_bfs_run 0) next_data_bfs_run 0))) /\ ((Znth (Znth e next_data_bfs_run 0) next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ” 
  &&  “ ((((Znth e next_data_bfs_run 0) <> (-1)) /\ ((Znth (Znth (Znth e next_data_bfs_run 0) to_data_bfs_run 0) dist_data 0) < 0)) -> ((r + 1 ) < nv_bfs_run)) ” 
  &&  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v (Znth e next_data_bfs_run 0) ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 (r + 1 ) queue_data )
  **  (IntArray.undef_seg q (r + 1 ) nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
) \/
(
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data_2: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data_2)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  TT && emp 
|--
  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far (app (queue_data_2) ((cons ((Znth e to_data_bfs_run 0)) ((@nil Z))))) (replace_Znth ((Znth e to_data_bfs_run 0)) (v) (parent_data_2)) (replace_Znth ((Znth e to_data_bfs_run 0)) (((Znth v dist_data_2 0) + 1 )) (dist_data_2)) head_data_bfs_run to_data_bfs_run next_data_bfs_run v (Znth e next_data_bfs_run 0) ) ” 
  &&  “ ((((Znth e next_data_bfs_run 0) <> (-1)) /\ ((Znth (Znth (Znth e next_data_bfs_run 0) to_data_bfs_run 0) (replace_Znth ((Znth e to_data_bfs_run 0)) (((Znth v dist_data_2 0) + 1 )) (dist_data_2)) 0) < 0)) -> ((r + 1 ) < nv_bfs_run)) ” 
  &&  “ (((Znth e next_data_bfs_run 0) <> (-1)) -> ((((0 <= (Znth (Znth e next_data_bfs_run 0) to_data_bfs_run 0)) /\ ((Znth (Znth e next_data_bfs_run 0) to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth (Znth e next_data_bfs_run 0) next_data_bfs_run 0))) /\ ((Znth (Znth e next_data_bfs_run 0) next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ” 
  &&  “ ((r + 1 ) = (Zlength ((app (queue_data_2) ((cons ((Znth e to_data_bfs_run 0)) ((@nil Z)))))))) ”
  &&  emp
).

Definition bfs_entail_wit_5_1_split_goal_1 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data_2: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data_2)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far (app (queue_data_2) ((cons ((Znth e to_data_bfs_run 0)) ((@nil Z))))) (replace_Znth ((Znth e to_data_bfs_run 0)) (v) (parent_data_2)) (replace_Znth ((Znth e to_data_bfs_run 0)) (((Znth v dist_data_2 0) + 1 )) (dist_data_2)) head_data_bfs_run to_data_bfs_run next_data_bfs_run v (Znth e next_data_bfs_run 0) )
.

Definition bfs_entail_wit_5_1_split_goal_2 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data_2: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data_2)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  ((((Znth e next_data_bfs_run 0) <> (-1)) /\ ((Znth (Znth (Znth e next_data_bfs_run 0) to_data_bfs_run 0) (replace_Znth ((Znth e to_data_bfs_run 0)) (((Znth v dist_data_2 0) + 1 )) (dist_data_2)) 0) < 0)) -> ((r + 1 ) < nv_bfs_run))
.

Definition bfs_entail_wit_5_1_split_goal_3 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data_2: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data_2)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (((Znth e next_data_bfs_run 0) <> (-1)) -> ((((0 <= (Znth (Znth e next_data_bfs_run 0) to_data_bfs_run 0)) /\ ((Znth (Znth e next_data_bfs_run 0) to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth (Znth e next_data_bfs_run 0) next_data_bfs_run 0))) /\ ((Znth (Znth e next_data_bfs_run 0) next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))
.

Definition bfs_entail_wit_5_1_split_goal_4 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data_2: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data_2)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  ((r + 1 ) = (Zlength ((app (queue_data_2) ((cons ((Znth e to_data_bfs_run 0)) ((@nil Z))))))))
.

Definition bfs_entail_wit_5_2 := 
(
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data_2: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) >= 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data_2)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.full dist_pre nv_bfs_run dist_data_2 )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data_2 )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data_2 )
|--
  EX (parent_data: (@list Z))  (dist_data: (@list Z))  (queue_data: (@list Z)) ,
  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 < l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ ((-1) <= (Znth e next_data_bfs_run 0)) ” 
  &&  “ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )) ” 
  &&  “ (((Znth e next_data_bfs_run 0) <> (-1)) -> ((((0 <= (Znth (Znth e next_data_bfs_run 0) to_data_bfs_run 0)) /\ ((Znth (Znth e next_data_bfs_run 0) to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth (Znth e next_data_bfs_run 0) next_data_bfs_run 0))) /\ ((Znth (Znth e next_data_bfs_run 0) next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ” 
  &&  “ ((((Znth e next_data_bfs_run 0) <> (-1)) /\ ((Znth (Znth (Znth e next_data_bfs_run 0) to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run)) ” 
  &&  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v (Znth e next_data_bfs_run 0) ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
) \/
(
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data_2: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) >= 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data_2)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  TT && emp 
|--
  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run v (Znth e next_data_bfs_run 0) ) ” 
  &&  “ ((((Znth e next_data_bfs_run 0) <> (-1)) /\ ((Znth (Znth (Znth e next_data_bfs_run 0) to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run)) ” 
  &&  “ (((Znth e next_data_bfs_run 0) <> (-1)) -> ((((0 <= (Znth (Znth e next_data_bfs_run 0) to_data_bfs_run 0)) /\ ((Znth (Znth e next_data_bfs_run 0) to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth (Znth e next_data_bfs_run 0) next_data_bfs_run 0))) /\ ((Znth (Znth e next_data_bfs_run 0) next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ”
  &&  emp
).

Definition bfs_entail_wit_5_2_split_goal_1 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data_2: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) >= 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data_2)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run v (Znth e next_data_bfs_run 0) )
.

Definition bfs_entail_wit_5_2_split_goal_2 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data_2: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) >= 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data_2)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  ((((Znth e next_data_bfs_run 0) <> (-1)) /\ ((Znth (Znth (Znth e next_data_bfs_run 0) to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run))
.

Definition bfs_entail_wit_5_2_split_goal_3 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data_2: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) >= 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data_2)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (((Znth e next_data_bfs_run 0) <> (-1)) -> ((((0 <= (Znth (Znth e next_data_bfs_run 0) to_data_bfs_run 0)) /\ ((Znth (Znth e next_data_bfs_run 0) to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth (Znth e next_data_bfs_run 0) next_data_bfs_run 0))) /\ ((Znth (Znth e next_data_bfs_run 0) next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))
.

Definition bfs_entail_wit_6 := 
(
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data_2: (@list Z)) (r: Z) (l: Z) (PreH1 : (e = (-1))) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH5 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH6 : (0 < l)) (PreH7 : (l <= r)) (PreH8 : (r = (Zlength (queue_data_2)))) (PreH9 : (r <= nv_bfs_run)) (PreH10 : (0 <= v)) (PreH11 : (v < nv_bfs_run)) (PreH12 : (0 <= far)) (PreH13 : (far < nv_bfs_run)) (PreH14 : ((-1) <= e)) (PreH15 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH16 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH17 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run))) (PreH18 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data_2 )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data_2 )
  **  (IntArray.full dist_pre nv_bfs_run dist_data_2 )
|--
  EX (parent_data: (@list Z))  (dist_data: (@list Z))  (queue_data: (@list Z)) ,
  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 <= l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run))) ” 
  &&  “ (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
) \/
(
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data_2: (@list Z)) (r: Z) (l: Z) (PreH1 : (e = (-1))) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH5 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH6 : (0 < l)) (PreH7 : (l <= r)) (PreH8 : (r = (Zlength (queue_data_2)))) (PreH9 : (r <= nv_bfs_run)) (PreH10 : (0 <= v)) (PreH11 : (v < nv_bfs_run)) (PreH12 : (0 <= far)) (PreH13 : (far < nv_bfs_run)) (PreH14 : ((-1) <= e)) (PreH15 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH16 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH17 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run))) (PreH18 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  TT && emp 
|--
  “ (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 ) ” 
  &&  “ forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data_2 0)) /\ ((Znth qindex queue_data_2 0) < nv_bfs_run))) ”
  &&  emp
).

Definition bfs_entail_wit_6_split_goal_1 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data_2: (@list Z)) (r: Z) (l: Z) (PreH1 : (e = (-1))) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH5 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH6 : (0 < l)) (PreH7 : (l <= r)) (PreH8 : (r = (Zlength (queue_data_2)))) (PreH9 : (r <= nv_bfs_run)) (PreH10 : (0 <= v)) (PreH11 : (v < nv_bfs_run)) (PreH12 : (0 <= far)) (PreH13 : (far < nv_bfs_run)) (PreH14 : ((-1) <= e)) (PreH15 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH16 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH17 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run))) (PreH18 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 )
.

Definition bfs_entail_wit_6_split_goal_2 := 
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data_2: (@list Z)) (r: Z) (l: Z) (PreH1 : (e = (-1))) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH5 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH6 : (0 < l)) (PreH7 : (l <= r)) (PreH8 : (r = (Zlength (queue_data_2)))) (PreH9 : (r <= nv_bfs_run)) (PreH10 : (0 <= v)) (PreH11 : (v < nv_bfs_run)) (PreH12 : (0 <= far)) (PreH13 : (far < nv_bfs_run)) (PreH14 : ((-1) <= e)) (PreH15 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH16 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH17 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data_2 0) < 0)) -> (r < nv_bfs_run))) (PreH18 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data_2 0)) /\ ((Znth qindex queue_data_2 0) < nv_bfs_run)))
.

Definition bfs_entail_wit_7 := 
(
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (far: Z) (queue_data_2: (@list Z)) (r: Z) (l: Z) (PreH1 : (l >= r)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH5 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH6 : (0 <= l)) (PreH7 : (l <= r)) (PreH8 : (r = (Zlength (queue_data_2)))) (PreH9 : (r <= nv_bfs_run)) (PreH10 : (0 <= far)) (PreH11 : (far < nv_bfs_run)) (PreH12 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data_2 0)) /\ ((Znth qindex queue_data_2 0) < nv_bfs_run)))) (PreH13 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 )) ,
  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data_2 )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data_2 )
  **  (IntArray.full dist_pre nv_bfs_run dist_data_2 )
|--
  EX (parent_data: (@list Z))  (dist_data: (@list Z))  (queue_data: (@list Z)) ,
  “ (1 <= nv_bfs_run) ” 
  &&  “ ((Zlength (queue_data)) = nv_bfs_run) ” 
  &&  “ (BFSResult nv_bfs_run edges_bfs_run src_pre parent_data dist_data far ) ”
  &&  ((( &( "l" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "r" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.full q nv_bfs_run queue_data )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
) \/
(
forall (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (far: Z) (queue_data_2: (@list Z)) (r: Z) (l: Z) (PreH1 : (l >= r)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH5 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH6 : (0 <= l)) (PreH7 : (l <= r)) (PreH8 : (r = (Zlength (queue_data_2)))) (PreH9 : (r <= nv_bfs_run)) (PreH10 : (0 <= far)) (PreH11 : (far < nv_bfs_run)) (PreH12 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data_2 0)) /\ ((Znth qindex queue_data_2 0) < nv_bfs_run)))) (PreH13 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data_2 parent_data_2 dist_data_2 )) ,
  (IntArray.seg q 0 r queue_data_2 )
  **  (IntArray.undef_seg q r nv_bfs_run )
|--
  EX (queue_data: (@list Z)) ,
  “ (r = nv_bfs_run) ” 
  &&  “ (l = nv_bfs_run) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ ((Zlength (queue_data)) = nv_bfs_run) ” 
  &&  “ (BFSResult nv_bfs_run edges_bfs_run src_pre parent_data_2 dist_data_2 far ) ”
  &&  (IntArray.full q nv_bfs_run queue_data )
).

Definition bfs_return_wit_1 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (queue_data: (@list Z)) (parent_data_2: (@list Z)) (dist_data_2: (@list Z)) (far: Z) (PreH1 : (1 <= nv_bfs_run)) (PreH2 : ((Zlength (queue_data)) = nv_bfs_run)) (PreH3 : (BFSResult nv_bfs_run edges_bfs_run src_pre parent_data_2 dist_data_2 far )) ,
  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data_2 )
  **  (IntArray.full dist_pre nv_bfs_run dist_data_2 )
|--
  EX (parent_data: (@list Z))  (dist_data: (@list Z)) ,
  “ (BFSResult nv_bfs_run edges_bfs_run src_pre parent_data dist_data far ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
.

Definition bfs_partial_solve_wit_1_pure := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (PreH1 : (1 <= nv_bfs_run)) (PreH2 : (nv_bfs_run <= 100000)) (PreH3 : (0 <= src_pre)) (PreH4 : (src_pre < nv_bfs_run)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) ,
  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.full_shape parent_pre nv_bfs_run )
  **  (IntArray.full_shape dist_pre nv_bfs_run )
|--
  “ (0 <= nv_bfs_run) ” 
  &&  “ ((nv_bfs_run * sizeof(INT) ) = (nv_bfs_run * sizeof(INT) )) ”
.

Definition bfs_partial_solve_wit_1_aux := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (PreH1 : (1 <= nv_bfs_run)) (PreH2 : (nv_bfs_run <= 100000)) (PreH3 : (0 <= src_pre)) (PreH4 : (src_pre < nv_bfs_run)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) ,
  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.full_shape parent_pre nv_bfs_run )
  **  (IntArray.full_shape dist_pre nv_bfs_run )
|--
  “ (0 <= nv_bfs_run) ” 
  &&  “ ((nv_bfs_run * sizeof(INT) ) = (nv_bfs_run * sizeof(INT) )) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (0 <= src_pre) ” 
  &&  “ (src_pre < nv_bfs_run) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.full_shape parent_pre nv_bfs_run )
  **  (IntArray.full_shape dist_pre nv_bfs_run )
.

Definition bfs_partial_solve_wit_1 := bfs_partial_solve_wit_1_pure -> bfs_partial_solve_wit_1_aux.

Definition bfs_partial_solve_wit_2 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) ,
  (IntArray.undef_full retval nv_bfs_run )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.full_shape parent_pre nv_bfs_run )
  **  (IntArray.full_shape dist_pre nv_bfs_run )
|--
  “ (retval <> 0) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (0 <= src_pre) ” 
  &&  “ (src_pre < nv_bfs_run) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ”
  &&  (((retval + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg retval 1 nv_bfs_run )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.full_shape parent_pre nv_bfs_run )
  **  (IntArray.full_shape dist_pre nv_bfs_run )
.

Definition bfs_partial_solve_wit_3 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (dist_data: (@list Z)) (parent_data: (@list Z)) (i: Z) (r: Z) (l: Z) (PreH1 : (i < nv_bfs_run)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH8 : (l = 0)) (PreH9 : (r = 1)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv_bfs_run)) (PreH12 : ((Zlength (parent_data)) = nv_bfs_run)) (PreH13 : ((Zlength (dist_data)) = nv_bfs_run)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data 0) = (-1)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data 0) = (-1)))) ,
  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 1 (cons (src_pre) ((@nil Z))) )
  **  (IntArray.undef_seg q 1 nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
|--
  “ (i < nv_bfs_run) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (0 <= src_pre) ” 
  &&  “ (src_pre < nv_bfs_run) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (l = 0) ” 
  &&  “ (r = 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nv_bfs_run) ” 
  &&  “ ((Zlength (parent_data)) = nv_bfs_run) ” 
  &&  “ ((Zlength (dist_data)) = nv_bfs_run) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data 0) = (-1))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data 0) = (-1))) ”
  &&  (((dist_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dist_pre i 0 nv_bfs_run dist_data )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 1 (cons (src_pre) ((@nil Z))) )
  **  (IntArray.undef_seg q 1 nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
.

Definition bfs_partial_solve_wit_4 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (dist_data: (@list Z)) (parent_data: (@list Z)) (i: Z) (r: Z) (l: Z) (PreH1 : (i < nv_bfs_run)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH8 : (l = 0)) (PreH9 : (r = 1)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv_bfs_run)) (PreH12 : ((Zlength (parent_data)) = nv_bfs_run)) (PreH13 : ((Zlength (dist_data)) = nv_bfs_run)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data 0) = (-1)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data 0) = (-1)))) ,
  (IntArray.full dist_pre nv_bfs_run (replace_Znth (i) ((-1)) (dist_data)) )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 1 (cons (src_pre) ((@nil Z))) )
  **  (IntArray.undef_seg q 1 nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
|--
  “ (i < nv_bfs_run) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (0 <= src_pre) ” 
  &&  “ (src_pre < nv_bfs_run) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (l = 0) ” 
  &&  “ (r = 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nv_bfs_run) ” 
  &&  “ ((Zlength (parent_data)) = nv_bfs_run) ” 
  &&  “ ((Zlength (dist_data)) = nv_bfs_run) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data 0) = (-1))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data 0) = (-1))) ”
  &&  (((parent_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i parent_pre i 0 nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run (replace_Znth (i) ((-1)) (dist_data)) )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 1 (cons (src_pre) ((@nil Z))) )
  **  (IntArray.undef_seg q 1 nv_bfs_run )
.

Definition bfs_partial_solve_wit_5 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (dist_data: (@list Z)) (parent_data: (@list Z)) (i: Z) (r: Z) (l: Z) (PreH1 : (i >= nv_bfs_run)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (0 <= src_pre)) (PreH5 : (src_pre < nv_bfs_run)) (PreH6 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH7 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH8 : (l = 0)) (PreH9 : (r = 1)) (PreH10 : (0 <= i)) (PreH11 : (i <= nv_bfs_run)) (PreH12 : ((Zlength (parent_data)) = nv_bfs_run)) (PreH13 : ((Zlength (dist_data)) = nv_bfs_run)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data 0) = (-1)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data 0) = (-1)))) ,
  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 1 (cons (src_pre) ((@nil Z))) )
  **  (IntArray.undef_seg q 1 nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
|--
  “ (i >= nv_bfs_run) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (0 <= src_pre) ” 
  &&  “ (src_pre < nv_bfs_run) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (l = 0) ” 
  &&  “ (r = 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nv_bfs_run) ” 
  &&  “ ((Zlength (parent_data)) = nv_bfs_run) ” 
  &&  “ ((Zlength (dist_data)) = nv_bfs_run) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j parent_data 0) = (-1))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 dist_data 0) = (-1))) ”
  &&  (((dist_pre + (src_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dist_pre src_pre 0 nv_bfs_run dist_data )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 1 (cons (src_pre) ((@nil Z))) )
  **  (IntArray.undef_seg q 1 nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
.

Definition bfs_partial_solve_wit_6 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : (l < r)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH5 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH6 : (0 <= l)) (PreH7 : (l <= r)) (PreH8 : (r = (Zlength (queue_data)))) (PreH9 : (r <= nv_bfs_run)) (PreH10 : (0 <= far)) (PreH11 : (far < nv_bfs_run)) (PreH12 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH13 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data )) ,
  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
|--
  “ (l < r) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 <= l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run))) ” 
  &&  “ (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data ) ”
  &&  (((q + (l * sizeof(INT)))) # Int  |-> (Znth (l - 0 ) queue_data 0))
  **  (IntArray.missing_i q l 0 r queue_data )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
.

Definition bfs_partial_solve_wit_7 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : (l < r)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH5 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH6 : (0 <= l)) (PreH7 : (l <= r)) (PreH8 : (r = (Zlength (queue_data)))) (PreH9 : (r <= nv_bfs_run)) (PreH10 : (0 <= far)) (PreH11 : (far < nv_bfs_run)) (PreH12 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH13 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data )) ,
  (IntArray.seg q 0 r queue_data )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
|--
  “ (l < r) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 <= l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run))) ” 
  &&  “ (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data ) ”
  &&  (((dist_pre + ((Znth (l - 0 ) queue_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth (l - 0 ) queue_data 0) dist_data 0))
  **  (IntArray.missing_i dist_pre (Znth (l - 0 ) queue_data 0) 0 nv_bfs_run dist_data )
  **  (IntArray.seg q 0 r queue_data )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
.

Definition bfs_partial_solve_wit_8 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : (l < r)) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH5 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH6 : (0 <= l)) (PreH7 : (l <= r)) (PreH8 : (r = (Zlength (queue_data)))) (PreH9 : (r <= nv_bfs_run)) (PreH10 : (0 <= far)) (PreH11 : (far < nv_bfs_run)) (PreH12 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH13 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data )) ,
  (IntArray.full dist_pre nv_bfs_run dist_data )
  **  (IntArray.seg q 0 r queue_data )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
|--
  “ (l < r) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 <= l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run))) ” 
  &&  “ (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data ) ”
  &&  (((dist_pre + (far * sizeof(INT)))) # Int  |-> (Znth far dist_data 0))
  **  (IntArray.missing_i dist_pre far 0 nv_bfs_run dist_data )
  **  (IntArray.seg q 0 r queue_data )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
.

Definition bfs_partial_solve_wit_9 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth (l - 0 ) queue_data 0) dist_data 0) > (Znth far dist_data 0))) (PreH2 : (l < r)) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 <= l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= far)) (PreH12 : (far < nv_bfs_run)) (PreH13 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH14 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data )) ,
  (IntArray.full dist_pre nv_bfs_run dist_data )
  **  (IntArray.seg q 0 r queue_data )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
|--
  “ ((Znth (Znth (l - 0 ) queue_data 0) dist_data 0) > (Znth far dist_data 0)) ” 
  &&  “ (l < r) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 <= l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run))) ” 
  &&  “ (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data ) ”
  &&  (((head_p_bfs_run + ((Znth (l - 0 ) queue_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0))
  **  (IntArray.missing_i head_p_bfs_run (Znth (l - 0 ) queue_data 0) 0 nv_bfs_run head_data_bfs_run )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
  **  (IntArray.seg q 0 r queue_data )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
.

Definition bfs_partial_solve_wit_10 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (far: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth (l - 0 ) queue_data 0) dist_data 0) <= (Znth far dist_data 0))) (PreH2 : (l < r)) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 <= l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= far)) (PreH12 : (far < nv_bfs_run)) (PreH13 : forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run)))) (PreH14 : (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data )) ,
  (IntArray.full dist_pre nv_bfs_run dist_data )
  **  (IntArray.seg q 0 r queue_data )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
|--
  “ ((Znth (Znth (l - 0 ) queue_data 0) dist_data 0) <= (Znth far dist_data 0)) ” 
  &&  “ (l < r) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 <= l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ forall (qindex: Z) , (((0 <= qindex) /\ (qindex < r)) -> ((0 <= (Znth qindex queue_data 0)) /\ ((Znth qindex queue_data 0) < nv_bfs_run))) ” 
  &&  “ (BFSQueueState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data ) ”
  &&  (((head_p_bfs_run + ((Znth (l - 0 ) queue_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth (l - 0 ) queue_data 0) head_data_bfs_run 0))
  **  (IntArray.missing_i head_p_bfs_run (Znth (l - 0 ) queue_data 0) 0 nv_bfs_run head_data_bfs_run )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
  **  (IntArray.seg q 0 r queue_data )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
.

Definition bfs_partial_solve_wit_11 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : (e <> (-1))) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH5 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH6 : (0 < l)) (PreH7 : (l <= r)) (PreH8 : (r = (Zlength (queue_data)))) (PreH9 : (r <= nv_bfs_run)) (PreH10 : (0 <= v)) (PreH11 : (v < nv_bfs_run)) (PreH12 : (0 <= far)) (PreH13 : (far < nv_bfs_run)) (PreH14 : ((-1) <= e)) (PreH15 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH16 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH17 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH18 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
|--
  “ (e <> (-1)) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 < l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ ((-1) <= e) ” 
  &&  “ (e < ((2 * nv_bfs_run ) - 2 )) ” 
  &&  “ ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ” 
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run)) ” 
  &&  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e ) ”
  &&  (((to_p_bfs_run + (e * sizeof(INT)))) # Int  |-> (Znth e to_data_bfs_run 0))
  **  (IntArray.missing_i to_p_bfs_run e 0 ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
.

Definition bfs_partial_solve_wit_12 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : (e <> (-1))) (PreH2 : (1 <= nv_bfs_run)) (PreH3 : (nv_bfs_run <= 100000)) (PreH4 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH5 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH6 : (0 < l)) (PreH7 : (l <= r)) (PreH8 : (r = (Zlength (queue_data)))) (PreH9 : (r <= nv_bfs_run)) (PreH10 : (0 <= v)) (PreH11 : (v < nv_bfs_run)) (PreH12 : (0 <= far)) (PreH13 : (far < nv_bfs_run)) (PreH14 : ((-1) <= e)) (PreH15 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH16 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH17 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH18 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
|--
  “ (e <> (-1)) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 < l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ ((-1) <= e) ” 
  &&  “ (e < ((2 * nv_bfs_run ) - 2 )) ” 
  &&  “ ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ” 
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run)) ” 
  &&  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e ) ”
  &&  (((dist_pre + ((Znth e to_data_bfs_run 0) * sizeof(INT)))) # Int  |-> (Znth (Znth e to_data_bfs_run 0) dist_data 0))
  **  (IntArray.missing_i dist_pre (Znth e to_data_bfs_run 0) 0 nv_bfs_run dist_data )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
.

Definition bfs_partial_solve_wit_13 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.full dist_pre nv_bfs_run dist_data )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
|--
  “ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0) ” 
  &&  “ (e <> (-1)) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 < l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ ((-1) <= e) ” 
  &&  “ (e < ((2 * nv_bfs_run ) - 2 )) ” 
  &&  “ ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ” 
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run)) ” 
  &&  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e ) ”
  &&  (((to_p_bfs_run + (e * sizeof(INT)))) # Int  |-> (Znth e to_data_bfs_run 0))
  **  (IntArray.missing_i to_p_bfs_run e 0 ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
.

Definition bfs_partial_solve_wit_14 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
|--
  “ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0) ” 
  &&  “ (e <> (-1)) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 < l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ ((-1) <= e) ” 
  &&  “ (e < ((2 * nv_bfs_run ) - 2 )) ” 
  &&  “ ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ” 
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run)) ” 
  &&  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e ) ”
  &&  (((dist_pre + (v * sizeof(INT)))) # Int  |-> (Znth v dist_data 0))
  **  (IntArray.missing_i dist_pre v 0 nv_bfs_run dist_data )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
.

Definition bfs_partial_solve_wit_15 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.full dist_pre nv_bfs_run dist_data )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
|--
  “ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0) ” 
  &&  “ (e <> (-1)) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 < l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ ((-1) <= e) ” 
  &&  “ (e < ((2 * nv_bfs_run ) - 2 )) ” 
  &&  “ ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ” 
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run)) ” 
  &&  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e ) ”
  &&  (((dist_pre + ((Znth e to_data_bfs_run 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dist_pre (Znth e to_data_bfs_run 0) 0 nv_bfs_run dist_data )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
.

Definition bfs_partial_solve_wit_16 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.full dist_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (((Znth v dist_data 0) + 1 )) (dist_data)) )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
|--
  “ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0) ” 
  &&  “ (e <> (-1)) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 < l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ ((-1) <= e) ” 
  &&  “ (e < ((2 * nv_bfs_run ) - 2 )) ” 
  &&  “ ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ” 
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run)) ” 
  &&  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e ) ”
  &&  (((to_p_bfs_run + (e * sizeof(INT)))) # Int  |-> (Znth e to_data_bfs_run 0))
  **  (IntArray.missing_i to_p_bfs_run e 0 ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full dist_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (((Znth v dist_data 0) + 1 )) (dist_data)) )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
.

Definition bfs_partial_solve_wit_17 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full dist_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (((Znth v dist_data 0) + 1 )) (dist_data)) )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
|--
  “ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0) ” 
  &&  “ (e <> (-1)) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 < l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ ((-1) <= e) ” 
  &&  “ (e < ((2 * nv_bfs_run ) - 2 )) ” 
  &&  “ ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ” 
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run)) ” 
  &&  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e ) ”
  &&  (((parent_pre + ((Znth e to_data_bfs_run 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i parent_pre (Znth e to_data_bfs_run 0) 0 nv_bfs_run parent_data )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full dist_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (((Znth v dist_data 0) + 1 )) (dist_data)) )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
.

Definition bfs_partial_solve_wit_18 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.full parent_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (v) (parent_data)) )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full dist_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (((Znth v dist_data 0) + 1 )) (dist_data)) )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
|--
  “ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0) ” 
  &&  “ (e <> (-1)) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 < l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ ((-1) <= e) ” 
  &&  “ (e < ((2 * nv_bfs_run ) - 2 )) ” 
  &&  “ ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ” 
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run)) ” 
  &&  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e ) ”
  &&  (((to_p_bfs_run + (e * sizeof(INT)))) # Int  |-> (Znth e to_data_bfs_run 0))
  **  (IntArray.missing_i to_p_bfs_run e 0 ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (v) (parent_data)) )
  **  (IntArray.full dist_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (((Znth v dist_data 0) + 1 )) (dist_data)) )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
.

Definition bfs_partial_solve_wit_19 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (v) (parent_data)) )
  **  (IntArray.full dist_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (((Znth v dist_data 0) + 1 )) (dist_data)) )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
|--
  “ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0) ” 
  &&  “ (e <> (-1)) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 < l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ ((-1) <= e) ” 
  &&  “ (e < ((2 * nv_bfs_run ) - 2 )) ” 
  &&  “ ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ” 
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run)) ” 
  &&  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e ) ”
  &&  (((q + (r * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg q (r + 1 ) nv_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (v) (parent_data)) )
  **  (IntArray.full dist_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (((Znth v dist_data 0) + 1 )) (dist_data)) )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
.

Definition bfs_partial_solve_wit_20 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.seg q 0 (r + 1 ) (app (queue_data) ((cons ((Znth e to_data_bfs_run 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg q (r + 1 ) nv_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (v) (parent_data)) )
  **  (IntArray.full dist_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (((Znth v dist_data 0) + 1 )) (dist_data)) )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
|--
  “ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0) ” 
  &&  “ (e <> (-1)) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 < l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ ((-1) <= e) ” 
  &&  “ (e < ((2 * nv_bfs_run ) - 2 )) ” 
  &&  “ ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ” 
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run)) ” 
  &&  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e ) ”
  &&  (((next_p_bfs_run + (e * sizeof(INT)))) # Int  |-> (Znth e next_data_bfs_run 0))
  **  (IntArray.missing_i next_p_bfs_run e 0 ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 (r + 1 ) (app (queue_data) ((cons ((Znth e to_data_bfs_run 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg q (r + 1 ) nv_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (v) (parent_data)) )
  **  (IntArray.full dist_pre nv_bfs_run (replace_Znth ((Znth e to_data_bfs_run 0)) (((Znth v dist_data 0) + 1 )) (dist_data)) )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
.

Definition bfs_partial_solve_wit_21 := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (q: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (e: Z) (far: Z) (v: Z) (queue_data: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (Znth e to_data_bfs_run 0) dist_data 0) >= 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= nv_bfs_run)) (PreH4 : (nv_bfs_run <= 100000)) (PreH5 : (GraphPre nv_bfs_run edges_bfs_run )) (PreH6 : (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run )) (PreH7 : (0 < l)) (PreH8 : (l <= r)) (PreH9 : (r = (Zlength (queue_data)))) (PreH10 : (r <= nv_bfs_run)) (PreH11 : (0 <= v)) (PreH12 : (v < nv_bfs_run)) (PreH13 : (0 <= far)) (PreH14 : (far < nv_bfs_run)) (PreH15 : ((-1) <= e)) (PreH16 : (e < ((2 * nv_bfs_run ) - 2 ))) (PreH17 : ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 ))))) (PreH18 : (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run))) (PreH19 : (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e )) ,
  (IntArray.full dist_pre nv_bfs_run dist_data )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
|--
  “ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) >= 0) ” 
  &&  “ (e <> (-1)) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ (nv_bfs_run <= 100000) ” 
  &&  “ (GraphPre nv_bfs_run edges_bfs_run ) ” 
  &&  “ (AdjacencyModel nv_bfs_run edges_bfs_run head_data_bfs_run to_data_bfs_run next_data_bfs_run ) ” 
  &&  “ (0 < l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r = (Zlength (queue_data))) ” 
  &&  “ (r <= nv_bfs_run) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v < nv_bfs_run) ” 
  &&  “ (0 <= far) ” 
  &&  “ (far < nv_bfs_run) ” 
  &&  “ ((-1) <= e) ” 
  &&  “ (e < ((2 * nv_bfs_run ) - 2 )) ” 
  &&  “ ((e <> (-1)) -> ((((0 <= (Znth e to_data_bfs_run 0)) /\ ((Znth e to_data_bfs_run 0) < nv_bfs_run)) /\ ((-1) <= (Znth e next_data_bfs_run 0))) /\ ((Znth e next_data_bfs_run 0) < ((2 * nv_bfs_run ) - 2 )))) ” 
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e to_data_bfs_run 0) dist_data 0) < 0)) -> (r < nv_bfs_run)) ” 
  &&  “ (BFSAdjState nv_bfs_run edges_bfs_run src_pre l far queue_data parent_data dist_data head_data_bfs_run to_data_bfs_run next_data_bfs_run v e ) ”
  &&  (((next_p_bfs_run + (e * sizeof(INT)))) # Int  |-> (Znth e next_data_bfs_run 0))
  **  (IntArray.missing_i next_p_bfs_run e 0 ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.seg q 0 r queue_data )
  **  (IntArray.undef_seg q r nv_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
.

Definition bfs_partial_solve_wit_22_pure := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (queue_data: (@list Z)) (parent_data: (@list Z)) (dist_data: (@list Z)) (far: Z) (q: Z) (PreH1 : (1 <= nv_bfs_run)) (PreH2 : ((Zlength (queue_data)) = nv_bfs_run)) (PreH3 : (BFSResult nv_bfs_run edges_bfs_run src_pre parent_data dist_data far )) ,
  ((( &( "parent" ) )) # Ptr  |-> parent_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "src" ) )) # Int  |-> src_pre)
  **  ((( &( "l" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "r" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "far" ) )) # Int  |-> far)
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (IntArray.full q nv_bfs_run queue_data )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
|--
  “ (0 <= nv_bfs_run) ” 
  &&  “ ((Zlength (queue_data)) = nv_bfs_run) ”
.

Definition bfs_partial_solve_wit_22_aux := 
forall (dist_pre: Z) (parent_pre: Z) (src_pre: Z) (next_data_bfs_run: (@list Z)) (to_data_bfs_run: (@list Z)) (head_data_bfs_run: (@list Z)) (next_p_bfs_run: Z) (to_p_bfs_run: Z) (head_p_bfs_run: Z) (edges_bfs_run: (@list (Z * Z))) (nv_bfs_run: Z) (queue_data: (@list Z)) (parent_data: (@list Z)) (dist_data: (@list Z)) (far: Z) (q: Z) (PreH1 : (1 <= nv_bfs_run)) (PreH2 : ((Zlength (queue_data)) = nv_bfs_run)) (PreH3 : (BFSResult nv_bfs_run edges_bfs_run src_pre parent_data dist_data far )) ,
  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.full q nv_bfs_run queue_data )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
|--
  “ (0 <= nv_bfs_run) ” 
  &&  “ ((Zlength (queue_data)) = nv_bfs_run) ” 
  &&  “ (1 <= nv_bfs_run) ” 
  &&  “ ((Zlength (queue_data)) = nv_bfs_run) ” 
  &&  “ (BFSResult nv_bfs_run edges_bfs_run src_pre parent_data dist_data far ) ”
  &&  (IntArray.full q nv_bfs_run queue_data )
  **  ((( &( "n" ) )) # Int  |-> nv_bfs_run)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_bfs_run)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_bfs_run)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_bfs_run)
  **  (IntArray.full head_p_bfs_run nv_bfs_run head_data_bfs_run )
  **  (IntArray.full to_p_bfs_run ((2 * nv_bfs_run ) - 2 ) to_data_bfs_run )
  **  (IntArray.full next_p_bfs_run ((2 * nv_bfs_run ) - 2 ) next_data_bfs_run )
  **  (IntArray.full parent_pre nv_bfs_run parent_data )
  **  (IntArray.full dist_pre nv_bfs_run dist_data )
.

Definition bfs_partial_solve_wit_22 := bfs_partial_solve_wit_22_pure -> bfs_partial_solve_wit_22_aux.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (next_before: Z) (to_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= nv)) (PreH4 : (nv <= 100000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (edges)) = (nv - 1 ))) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH9 : (Pre nv k_pre edges )) (PreH10 : (nn_pre = nv)) (PreH11 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH12 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full retval_2 nv (repeat_Z (0) (nv)) )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> retval_2)
|--
  “ (((2 * nn_pre ) - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * nn_pre ) - 2 )) ”
.

Definition solver_safety_wit_2 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (next_before: Z) (to_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= nv)) (PreH4 : (nv <= 100000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (edges)) = (nv - 1 ))) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH9 : (Pre nv k_pre edges )) (PreH10 : (nn_pre = nv)) (PreH11 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH12 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full retval_2 nv (repeat_Z (0) (nv)) )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> retval_2)
|--
  “ ((2 * nn_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * nn_pre )) ”
.

Definition solver_safety_wit_3 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (next_before: Z) (to_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= nv)) (PreH4 : (nv <= 100000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (edges)) = (nv - 1 ))) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH9 : (Pre nv k_pre edges )) (PreH10 : (nn_pre = nv)) (PreH11 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH12 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full retval_2 nv (repeat_Z (0) (nv)) )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> retval_2)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_4 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (next_before: Z) (to_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= nv)) (PreH4 : (nv <= 100000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (edges)) = (nv - 1 ))) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH9 : (Pre nv k_pre edges )) (PreH10 : (nn_pre = nv)) (PreH11 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH12 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full retval_2 nv (repeat_Z (0) (nv)) )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> retval_2)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_5 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (next_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod_Z_Z (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= nv)) (PreH5 : (nv <= 100000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : ((Zlength (edges)) = (nv - 1 ))) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH10 : (Pre nv k_pre edges )) (PreH11 : (nn_pre = nv)) (PreH12 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH13 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH14 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.undef_full retval_3 ((2 * nv ) - 2 ) )
  **  (IntArray.full retval_2 nv (repeat_Z (0) (nv)) )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> retval_3)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> retval_2)
|--
  “ (((2 * nn_pre ) - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * nn_pre ) - 2 )) ”
.

Definition solver_safety_wit_6 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (next_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod_Z_Z (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= nv)) (PreH5 : (nv <= 100000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : ((Zlength (edges)) = (nv - 1 ))) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH10 : (Pre nv k_pre edges )) (PreH11 : (nn_pre = nv)) (PreH12 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH13 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH14 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.undef_full retval_3 ((2 * nv ) - 2 ) )
  **  (IntArray.full retval_2 nv (repeat_Z (0) (nv)) )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> retval_3)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> retval_2)
|--
  “ ((2 * nn_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * nn_pre )) ”
.

Definition solver_safety_wit_7 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (next_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod_Z_Z (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= nv)) (PreH5 : (nv <= 100000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : ((Zlength (edges)) = (nv - 1 ))) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH10 : (Pre nv k_pre edges )) (PreH11 : (nn_pre = nv)) (PreH12 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH13 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH14 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.undef_full retval_3 ((2 * nv ) - 2 ) )
  **  (IntArray.full retval_2 nv (repeat_Z (0) (nv)) )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> retval_3)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> retval_2)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_8 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (next_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod_Z_Z (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= nv)) (PreH5 : (nv <= 100000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : ((Zlength (edges)) = (nv - 1 ))) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH10 : (Pre nv k_pre edges )) (PreH11 : (nn_pre = nv)) (PreH12 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH13 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH14 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.undef_full retval_3 ((2 * nv ) - 2 ) )
  **  (IntArray.full retval_2 nv (repeat_Z (0) (nv)) )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> retval_3)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> retval_2)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_9 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z)  __default__Prod_Z_Z (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 100000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : ((Zlength (edges)) = (nv - 1 ))) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH11 : (Pre nv k_pre edges )) (PreH12 : (nn_pre = nv)) (PreH13 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH14 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH15 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_4 ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full retval_3 ((2 * nv ) - 2 ) )
  **  (IntArray.full retval_2 nv (repeat_Z (0) (nv)) )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> retval_3)
  **  ((( &( "nxt" ) )) # Ptr  |-> retval_4)
  **  ((( &( "deg" ) )) # Ptr  |-> retval_2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (head_init: (@list Z)) (i: Z)  __default__Prod_Z_Z (PreH1 : (i < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (GraphPre nv edges )) (PreH8 : (0 <= i)) (PreH9 : (i <= nv)) (PreH10 : ((Zlength (head_init)) = i)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.seg head_p 0 (i + 1 ) (app (head_init) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg head_p (i + 1 ) nv )
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.undef_full to_p ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv (repeat_Z (0) (nv)) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (head_init: (@list Z)) (i: Z)  __default__Prod_Z_Z (PreH1 : (i < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (GraphPre nv edges )) (PreH8 : (0 <= i)) (PreH9 : (i <= nv)) (PreH10 : ((Zlength (head_init)) = i)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.seg head_p 0 i head_init )
  **  (IntArray.undef_seg head_p i nv )
  **  (IntArray.undef_full to_p ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv (repeat_Z (0) (nv)) )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_12 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (head_init: (@list Z)) (i: Z)  __default__Prod_Z_Z (PreH1 : (i < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (GraphPre nv edges )) (PreH8 : (0 <= i)) (PreH9 : (i <= nv)) (PreH10 : ((Zlength (head_init)) = i)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.seg head_p 0 i head_init )
  **  (IntArray.undef_seg head_p i nv )
  **  (IntArray.undef_full to_p ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv (repeat_Z (0) (nv)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_13 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (head_init: (@list Z)) (i: Z)  __default__Prod_Z_Z (PreH1 : (i >= nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (GraphPre nv edges )) (PreH8 : (0 <= i)) (PreH9 : (i <= nv)) (PreH10 : ((Zlength (head_init)) = i)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  ((( &( "ec" ) )) # Int  |->_)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.seg head_p 0 i head_init )
  **  (IntArray.undef_seg head_p i nv )
  **  (IntArray.undef_full to_p ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv (repeat_Z (0) (nv)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (head_init: (@list Z)) (i: Z)  __default__Prod_Z_Z (PreH1 : (i >= nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (GraphPre nv edges )) (PreH8 : (0 <= i)) (PreH9 : (i <= nv)) (PreH10 : ((Zlength (head_init)) = i)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "ec" ) )) # Int  |-> 0)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.seg head_p 0 i head_init )
  **  (IntArray.undef_seg head_p i nv )
  **  (IntArray.undef_full to_p ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv (repeat_Z (0) (nv)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_15 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : (1 <= nv)) (PreH2 : (nv <= 100000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : (Pre nv k_pre edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (to_done)) = ec)) (PreH11 : ((Zlength (next_done)) = ec)) (PreH12 : ((Zlength (degree_data)) = nv)) (PreH13 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH14 : (DegreePrefix nv edges i degree_data )) (PreH15 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 ec to_done )
  **  (IntArray.undef_seg to_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv degree_data )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_16 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : (1 <= nv)) (PreH2 : (nv <= 100000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : (Pre nv k_pre edges )) (PreH6 : (0 <= i)) (PreH7 : (i <= (nv - 1 ))) (PreH8 : (ec = (2 * i ))) (PreH9 : ((Zlength (head_data)) = nv)) (PreH10 : ((Zlength (to_done)) = ec)) (PreH11 : ((Zlength (next_done)) = ec)) (PreH12 : ((Zlength (degree_data)) = nv)) (PreH13 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH14 : (DegreePrefix nv edges i degree_data )) (PreH15 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 ec to_done )
  **  (IntArray.undef_seg to_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv degree_data )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_17 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
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
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
|--
  “ ((ec + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ec + 1 )) ”
.

Definition solver_safety_wit_18 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
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
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ec" ) )) # Int  |-> (ec + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
|--
  “ (((ec + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((ec + 1 ) + 1 )) ”
.

Definition solver_safety_wit_19 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth i ev_data 0))
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "u" ) )) # Int  |-> (Znth i eu_data 0))
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ec" ) )) # Int  |-> ((ec + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
|--
  “ (((Znth (Znth i eu_data 0) degree_data 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (Znth i eu_data 0) degree_data 0) + 1 )) ”
) \/
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth i ev_data 0))
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "u" ) )) # Int  |-> (Znth i eu_data 0))
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ec" ) )) # Int  |-> ((ec + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
|--
  “ (((Znth (Znth i eu_data 0) degree_data 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (Znth i eu_data 0) degree_data 0) + 1 )) ”
).

Definition solver_safety_wit_19_split_goal_1 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth i ev_data 0))
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "u" ) )) # Int  |-> (Znth i eu_data 0))
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ec" ) )) # Int  |-> ((ec + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
|--
  “ (((Znth (Znth i eu_data 0) degree_data 0) + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_19_split_goal_2 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth i ev_data 0))
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "u" ) )) # Int  |-> (Znth i eu_data 0))
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ec" ) )) # Int  |-> ((ec + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
|--
  “ ((INT_MIN) <= ((Znth (Znth i eu_data 0) degree_data 0) + 1 )) ”
.

Definition solver_safety_wit_20 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full deg_p nv (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data 0) + 1 )) (degree_data)) )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth i ev_data 0))
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "u" ) )) # Int  |-> (Znth i eu_data 0))
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ec" ) )) # Int  |-> ((ec + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
|--
  “ (((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data 0) + 1 )) (degree_data)) 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data 0) + 1 )) (degree_data)) 0) + 1 )) ”
) \/
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full deg_p nv (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data 0) + 1 )) (degree_data)) )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth i ev_data 0))
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "u" ) )) # Int  |-> (Znth i eu_data 0))
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ec" ) )) # Int  |-> ((ec + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
|--
  “ (((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data 0) + 1 )) (degree_data)) 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data 0) + 1 )) (degree_data)) 0) + 1 )) ”
).

Definition solver_safety_wit_20_split_goal_1 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full deg_p nv (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data 0) + 1 )) (degree_data)) )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth i ev_data 0))
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "u" ) )) # Int  |-> (Znth i eu_data 0))
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ec" ) )) # Int  |-> ((ec + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
|--
  “ (((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data 0) + 1 )) (degree_data)) 0) + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_20_split_goal_2 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full deg_p nv (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data 0) + 1 )) (degree_data)) )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "v" ) )) # Int  |-> (Znth i ev_data 0))
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "u" ) )) # Int  |-> (Znth i eu_data 0))
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ec" ) )) # Int  |-> ((ec + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
|--
  “ ((INT_MIN) <= ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data 0) + 1 )) (degree_data)) 0) + 1 )) ”
.

Definition solver_safety_wit_21 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full deg_p nv (replace_Znth ((Znth i ev_data 0)) (((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data 0) + 1 )) (degree_data)) 0) + 1 )) ((replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data 0) + 1 )) (degree_data)))) )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ec" ) )) # Int  |-> ((ec + 1 ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_22 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= nv)) (PreH5 : (nv <= 100000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : (Pre nv k_pre edges )) (PreH9 : (GraphPre nv edges )) (PreH10 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH11 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  ((( &( "ok" ) )) # Int  |->_)
  **  (IntArray.full_shape retval_2 nv )
  **  ((( &( "d" ) )) # Ptr  |-> retval_2)
  **  (IntArray.full_shape retval nv )
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_23 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= nv)) (PreH5 : (nv <= 100000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : (Pre nv k_pre edges )) (PreH9 : (GraphPre nv edges )) (PreH10 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH11 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "ok" ) )) # Int  |-> 1)
  **  (IntArray.full_shape retval_2 nv )
  **  ((( &( "d" ) )) # Ptr  |-> retval_2)
  **  (IntArray.full_shape retval nv )
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_24 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (p: Z) (d: Z) (PreH1 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH2 : (BFSResult nv edges a second_parent second_dist b )) (PreH3 : (0 <= a)) (PreH4 : (a < nv)) (PreH5 : (0 <= b)) (PreH6 : (b < nv)) (PreH7 : (ok = 1)) (PreH8 : (ec = ((2 * nv ) - 2 ))) (PreH9 : (1 <= nv)) (PreH10 : (nv <= 100000)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (GraphPre nv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  (IntArray.full d nv second_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv second_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ ((2 * k_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * k_pre )) ”
.

Definition solver_safety_wit_25 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (p: Z) (d: Z) (PreH1 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH2 : (BFSResult nv edges a second_parent second_dist b )) (PreH3 : (0 <= a)) (PreH4 : (a < nv)) (PreH5 : (0 <= b)) (PreH6 : (b < nv)) (PreH7 : (ok = 1)) (PreH8 : (ec = ((2 * nv ) - 2 ))) (PreH9 : (1 <= nv)) (PreH10 : (nv <= 100000)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (GraphPre nv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  (IntArray.full d nv second_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv second_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_26 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (p: Z) (d: Z) (PreH1 : ((Znth b second_dist 0) <> (2 * k_pre ))) (PreH2 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH3 : (BFSResult nv edges a second_parent second_dist b )) (PreH4 : (0 <= a)) (PreH5 : (a < nv)) (PreH6 : (0 <= b)) (PreH7 : (b < nv)) (PreH8 : (ok = 1)) (PreH9 : (ec = ((2 * nv ) - 2 ))) (PreH10 : (1 <= nv)) (PreH11 : (nv <= 100000)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (GraphPre nv edges )) (PreH15 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH16 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  (IntArray.full d nv second_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv second_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_27 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (p: Z) (d: Z) (PreH1 : ((Znth b second_dist 0) <> (2 * k_pre ))) (PreH2 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH3 : (BFSResult nv edges a second_parent second_dist b )) (PreH4 : (0 <= a)) (PreH5 : (a < nv)) (PreH6 : (0 <= b)) (PreH7 : (b < nv)) (PreH8 : (ok = 1)) (PreH9 : (ec = ((2 * nv ) - 2 ))) (PreH10 : (1 <= nv)) (PreH11 : (nv <= 100000)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (GraphPre nv edges )) (PreH15 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH16 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  ((( &( "i" ) )) # Int64  |->_)
  **  ((( &( "center" ) )) # Int  |-> b)
  **  (IntArray.full d nv second_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ok" ) )) # Int  |-> 0)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv second_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_28 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (p: Z) (d: Z) (PreH1 : ((Znth b second_dist 0) = (2 * k_pre ))) (PreH2 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH3 : (BFSResult nv edges a second_parent second_dist b )) (PreH4 : (0 <= a)) (PreH5 : (a < nv)) (PreH6 : (0 <= b)) (PreH7 : (b < nv)) (PreH8 : (ok = 1)) (PreH9 : (ec = ((2 * nv ) - 2 ))) (PreH10 : (1 <= nv)) (PreH11 : (nv <= 100000)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (GraphPre nv edges )) (PreH15 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH16 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  ((( &( "i" ) )) # Int64  |->_)
  **  ((( &( "center" ) )) # Int  |-> b)
  **  (IntArray.full d nv second_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv second_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_29 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (i: Z) (ok: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : (i < k_pre)) (PreH2 : (ok <> 0)) (PreH3 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH4 : (BFSResult nv edges a second_parent second_dist b )) (PreH5 : (GraphPre nv edges )) (PreH6 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH7 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH8 : (ec = ((2 * nv ) - 2 ))) (PreH9 : (1 <= nv)) (PreH10 : (nv <= 100000)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (DiameterDecision k_pre second_dist b ok )) (PreH14 : (0 <= i)) (PreH15 : (i <= k_pre)) (PreH16 : (0 <= center)) (PreH17 : (center < nv)) (PreH18 : (AncestorAfter second_parent b i center )) ,
  (IntArray.full p nv second_parent )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "i" ) )) # Int64  |-> i)
  **  ((( &( "center" ) )) # Int  |-> (Znth center second_parent 0))
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv second_dist )
|--
  “ ((i + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_30 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (i: Z) (ok: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : (i >= k_pre)) (PreH2 : (ok <> 0)) (PreH3 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH4 : (BFSResult nv edges a second_parent second_dist b )) (PreH5 : (GraphPre nv edges )) (PreH6 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH7 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH8 : (ec = ((2 * nv ) - 2 ))) (PreH9 : (1 <= nv)) (PreH10 : (nv <= 100000)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (DiameterDecision k_pre second_dist b ok )) (PreH14 : (0 <= i)) (PreH15 : (i <= k_pre)) (PreH16 : (0 <= center)) (PreH17 : (center < nv)) (PreH18 : (AncestorAfter second_parent b i center )) (PreH19 : (ok = 0)) ,
  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv second_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv second_dist )
|--
  “ False ”
.

Definition solver_safety_wit_31 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (i: Z) (ok: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : (ok = 0)) (PreH2 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH3 : (BFSResult nv edges a second_parent second_dist b )) (PreH4 : (GraphPre nv edges )) (PreH5 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH6 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH7 : (ec = ((2 * nv ) - 2 ))) (PreH8 : (1 <= nv)) (PreH9 : (nv <= 100000)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 1000000000)) (PreH12 : (DiameterDecision k_pre second_dist b ok )) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= center)) (PreH16 : (center < nv)) (PreH17 : (AncestorAfter second_parent b i center )) (PreH18 : (ok <> 0)) ,
  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv second_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv second_dist )
|--
  “ False ”
.

Definition solver_safety_wit_32 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (center: Z) (p: Z) (d: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (retval: Z) (PreH1 : (BFSResult nv edges center parent_data dist_data retval )) (PreH2 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH3 : (BFSResult nv edges a second_parent second_dist b )) (PreH4 : (GraphPre nv edges )) (PreH5 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH6 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH7 : (ok = 1)) (PreH8 : (1 <= nv)) (PreH9 : (nv <= 100000)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 1000000000)) (PreH12 : (ec = ((2 * nv ) - 2 ))) (PreH13 : (0 <= center)) (PreH14 : (center < nv)) (PreH15 : (AncestorAfter second_parent b k_pre center )) (PreH16 : ((Znth b second_dist 0) = (2 * k_pre ))) ,
  ((( &( "v" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full p nv parent_data )
  **  (IntArray.full d nv dist_data )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_33 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (i: Z) (ok: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : (ok = 0)) (PreH2 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH3 : (BFSResult nv edges a second_parent second_dist b )) (PreH4 : (GraphPre nv edges )) (PreH5 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH6 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH7 : (ec = ((2 * nv ) - 2 ))) (PreH8 : (1 <= nv)) (PreH9 : (nv <= 100000)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 1000000000)) (PreH12 : (DiameterDecision k_pre second_dist b ok )) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= center)) (PreH16 : (center < nv)) (PreH17 : (AncestorAfter second_parent b i center )) (PreH18 : (ok = 0)) ,
  ((( &( "v" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv second_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv second_dist )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_34 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : ((Znth v center_dist 0) = k_pre)) (PreH2 : ((Znth v center_dist 0) <= k_pre)) (PreH3 : (v < nv)) (PreH4 : (ok <> 0)) (PreH5 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH6 : (BFSResult nv edges a second_parent second_dist b )) (PreH7 : (GraphPre nv edges )) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 1000000000)) (PreH10 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH11 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH12 : (ec = ((2 * nv ) - 2 ))) (PreH13 : (0 <= v)) (PreH14 : (v <= nv)) (PreH15 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full d nv center_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_35 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : ((Znth v center_dist 0) >= k_pre)) (PreH2 : ((Znth v center_dist 0) <> k_pre)) (PreH3 : ((Znth v center_dist 0) <= k_pre)) (PreH4 : (v < nv)) (PreH5 : (ok <> 0)) (PreH6 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH7 : (BFSResult nv edges a second_parent second_dist b )) (PreH8 : (GraphPre nv edges )) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 1000000000)) (PreH11 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH12 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH13 : (ec = ((2 * nv ) - 2 ))) (PreH14 : (0 <= v)) (PreH15 : (v <= nv)) (PreH16 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full d nv center_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ False ”
.

Definition solver_safety_wit_36 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : ((Znth v center_dist 0) < k_pre)) (PreH2 : ((Znth v degree_data 0) = 1)) (PreH3 : ((Znth v center_dist 0) = k_pre)) (PreH4 : ((Znth v center_dist 0) <= k_pre)) (PreH5 : (v < nv)) (PreH6 : (ok <> 0)) (PreH7 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH8 : (BFSResult nv edges a second_parent second_dist b )) (PreH9 : (GraphPre nv edges )) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 1000000000)) (PreH12 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH13 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH14 : (ec = ((2 * nv ) - 2 ))) (PreH15 : (0 <= v)) (PreH16 : (v <= nv)) (PreH17 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full d nv center_dist )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ False ”
.

Definition solver_safety_wit_37 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : (v = center)) (PreH2 : ((Znth v center_dist 0) < k_pre)) (PreH3 : ((Znth v center_dist 0) <> k_pre)) (PreH4 : ((Znth v center_dist 0) <= k_pre)) (PreH5 : (v < nv)) (PreH6 : (ok <> 0)) (PreH7 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH8 : (BFSResult nv edges a second_parent second_dist b )) (PreH9 : (GraphPre nv edges )) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 1000000000)) (PreH12 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH13 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH14 : (ec = ((2 * nv ) - 2 ))) (PreH15 : (0 <= v)) (PreH16 : (v <= nv)) (PreH17 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full d nv center_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_38 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : (v <> center)) (PreH2 : ((Znth v degree_data 0) >= 3)) (PreH3 : (v = center)) (PreH4 : ((Znth v center_dist 0) < k_pre)) (PreH5 : ((Znth v center_dist 0) <> k_pre)) (PreH6 : ((Znth v center_dist 0) <= k_pre)) (PreH7 : (v < nv)) (PreH8 : (ok <> 0)) (PreH9 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH10 : (BFSResult nv edges a second_parent second_dist b )) (PreH11 : (GraphPre nv edges )) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH16 : (ec = ((2 * nv ) - 2 ))) (PreH17 : (0 <= v)) (PreH18 : (v <= nv)) (PreH19 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full d nv center_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ False ”
.

Definition solver_safety_wit_39 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : (v = center)) (PreH2 : (v <> center)) (PreH3 : ((Znth v center_dist 0) < k_pre)) (PreH4 : ((Znth v center_dist 0) <> k_pre)) (PreH5 : ((Znth v center_dist 0) <= k_pre)) (PreH6 : (v < nv)) (PreH7 : (ok <> 0)) (PreH8 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH9 : (BFSResult nv edges a second_parent second_dist b )) (PreH10 : (GraphPre nv edges )) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH15 : (ec = ((2 * nv ) - 2 ))) (PreH16 : (0 <= v)) (PreH17 : (v <= nv)) (PreH18 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full d nv center_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ False ”
.

Definition solver_safety_wit_40 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : (v <> center)) (PreH2 : (v <> center)) (PreH3 : ((Znth v center_dist 0) < k_pre)) (PreH4 : ((Znth v center_dist 0) <> k_pre)) (PreH5 : ((Znth v center_dist 0) <= k_pre)) (PreH6 : (v < nv)) (PreH7 : (ok <> 0)) (PreH8 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH9 : (BFSResult nv edges a second_parent second_dist b )) (PreH10 : (GraphPre nv edges )) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH15 : (ec = ((2 * nv ) - 2 ))) (PreH16 : (0 <= v)) (PreH17 : (v <= nv)) (PreH18 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full d nv center_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition solver_safety_wit_41 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : ((Znth v degree_data 0) <> 1)) (PreH2 : ((Znth v center_dist 0) = k_pre)) (PreH3 : ((Znth v center_dist 0) <= k_pre)) (PreH4 : (v < nv)) (PreH5 : (ok <> 0)) (PreH6 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH7 : (BFSResult nv edges a second_parent second_dist b )) (PreH8 : (GraphPre nv edges )) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 1000000000)) (PreH11 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH12 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH13 : (ec = ((2 * nv ) - 2 ))) (PreH14 : (0 <= v)) (PreH15 : (v <= nv)) (PreH16 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full d nv center_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_42 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : ((Znth v center_dist 0) > k_pre)) (PreH2 : (v < nv)) (PreH3 : (ok <> 0)) (PreH4 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH5 : (BFSResult nv edges a second_parent second_dist b )) (PreH6 : (GraphPre nv edges )) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH10 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH11 : (ec = ((2 * nv ) - 2 ))) (PreH12 : (0 <= v)) (PreH13 : (v <= nv)) (PreH14 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full d nv center_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_43 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : ((Znth v degree_data 0) < 3)) (PreH2 : (v = center)) (PreH3 : ((Znth v center_dist 0) < k_pre)) (PreH4 : ((Znth v center_dist 0) <> k_pre)) (PreH5 : ((Znth v center_dist 0) <= k_pre)) (PreH6 : (v < nv)) (PreH7 : (ok <> 0)) (PreH8 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH9 : (BFSResult nv edges a second_parent second_dist b )) (PreH10 : (GraphPre nv edges )) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH15 : (ec = ((2 * nv ) - 2 ))) (PreH16 : (0 <= v)) (PreH17 : (v <= nv)) (PreH18 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full d nv center_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_44 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : ((Znth v degree_data 0) < 4)) (PreH2 : (v <> center)) (PreH3 : (v <> center)) (PreH4 : ((Znth v center_dist 0) < k_pre)) (PreH5 : ((Znth v center_dist 0) <> k_pre)) (PreH6 : ((Znth v center_dist 0) <= k_pre)) (PreH7 : (v < nv)) (PreH8 : (ok <> 0)) (PreH9 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH10 : (BFSResult nv edges a second_parent second_dist b )) (PreH11 : (GraphPre nv edges )) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH16 : (ec = ((2 * nv ) - 2 ))) (PreH17 : (0 <= v)) (PreH18 : (v <= nv)) (PreH19 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full d nv center_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_45 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : ((Znth v degree_data 0) <> 1)) (PreH2 : ((Znth v center_dist 0) = k_pre)) (PreH3 : ((Znth v center_dist 0) <= k_pre)) (PreH4 : (v < nv)) (PreH5 : (ok <> 0)) (PreH6 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH7 : (BFSResult nv edges a second_parent second_dist b )) (PreH8 : (GraphPre nv edges )) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 1000000000)) (PreH11 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH12 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH13 : (ec = ((2 * nv ) - 2 ))) (PreH14 : (0 <= v)) (PreH15 : (v <= nv)) (PreH16 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full d nv center_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "ok" ) )) # Int  |-> 0)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition solver_safety_wit_46 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : ((Znth v center_dist 0) > k_pre)) (PreH2 : (v < nv)) (PreH3 : (ok <> 0)) (PreH4 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH5 : (BFSResult nv edges a second_parent second_dist b )) (PreH6 : (GraphPre nv edges )) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH10 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH11 : (ec = ((2 * nv ) - 2 ))) (PreH12 : (0 <= v)) (PreH13 : (v <= nv)) (PreH14 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full d nv center_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "ok" ) )) # Int  |-> 0)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition solver_safety_wit_47 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : ((Znth v degree_data 0) < 3)) (PreH2 : (v = center)) (PreH3 : ((Znth v center_dist 0) < k_pre)) (PreH4 : ((Znth v center_dist 0) <> k_pre)) (PreH5 : ((Znth v center_dist 0) <= k_pre)) (PreH6 : (v < nv)) (PreH7 : (ok <> 0)) (PreH8 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH9 : (BFSResult nv edges a second_parent second_dist b )) (PreH10 : (GraphPre nv edges )) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH15 : (ec = ((2 * nv ) - 2 ))) (PreH16 : (0 <= v)) (PreH17 : (v <= nv)) (PreH18 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full d nv center_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "ok" ) )) # Int  |-> 0)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition solver_safety_wit_48 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : ((Znth v degree_data 0) < 4)) (PreH2 : (v <> center)) (PreH3 : (v <> center)) (PreH4 : ((Znth v center_dist 0) < k_pre)) (PreH5 : ((Znth v center_dist 0) <> k_pre)) (PreH6 : ((Znth v center_dist 0) <= k_pre)) (PreH7 : (v < nv)) (PreH8 : (ok <> 0)) (PreH9 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH10 : (BFSResult nv edges a second_parent second_dist b )) (PreH11 : (GraphPre nv edges )) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH16 : (ec = ((2 * nv ) - 2 ))) (PreH17 : (0 <= v)) (PreH18 : (v <= nv)) (PreH19 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full d nv center_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "ok" ) )) # Int  |-> 0)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition solver_safety_wit_49 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : ((Znth v degree_data 0) >= 4)) (PreH2 : (v <> center)) (PreH3 : (v <> center)) (PreH4 : ((Znth v center_dist 0) < k_pre)) (PreH5 : ((Znth v center_dist 0) <> k_pre)) (PreH6 : ((Znth v center_dist 0) <= k_pre)) (PreH7 : (v < nv)) (PreH8 : (ok <> 0)) (PreH9 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH10 : (BFSResult nv edges a second_parent second_dist b )) (PreH11 : (GraphPre nv edges )) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH16 : (ec = ((2 * nv ) - 2 ))) (PreH17 : (0 <= v)) (PreH18 : (v <= nv)) (PreH19 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full d nv center_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition solver_safety_wit_50 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : (v = center)) (PreH2 : ((Znth v degree_data 0) >= 3)) (PreH3 : (v = center)) (PreH4 : ((Znth v center_dist 0) < k_pre)) (PreH5 : ((Znth v center_dist 0) <> k_pre)) (PreH6 : ((Znth v center_dist 0) <= k_pre)) (PreH7 : (v < nv)) (PreH8 : (ok <> 0)) (PreH9 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH10 : (BFSResult nv edges a second_parent second_dist b )) (PreH11 : (GraphPre nv edges )) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH16 : (ec = ((2 * nv ) - 2 ))) (PreH17 : (0 <= v)) (PreH18 : (v <= nv)) (PreH19 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full d nv center_dist )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition solver_safety_wit_51 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : ((Znth v center_dist 0) >= k_pre)) (PreH2 : ((Znth v degree_data 0) = 1)) (PreH3 : ((Znth v center_dist 0) = k_pre)) (PreH4 : ((Znth v center_dist 0) <= k_pre)) (PreH5 : (v < nv)) (PreH6 : (ok <> 0)) (PreH7 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH8 : (BFSResult nv edges a second_parent second_dist b )) (PreH9 : (GraphPre nv edges )) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 1000000000)) (PreH12 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH13 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH14 : (ec = ((2 * nv ) - 2 ))) (PreH15 : (0 <= v)) (PreH16 : (v <= nv)) (PreH17 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full d nv center_dist )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z)  __default__Prod_Z_Z (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 100000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : ((Zlength (edges)) = (nv - 1 ))) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH11 : (Pre nv k_pre edges )) (PreH12 : (nn_pre = nv)) (PreH13 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH14 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH15 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.undef_full retval_4 ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full retval_3 ((2 * nv ) - 2 ) )
  **  (IntArray.full retval_2 nv (repeat_Z (0) (nv)) )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> retval_3)
  **  ((( &( "nxt" ) )) # Ptr  |-> retval_4)
  **  ((( &( "deg" ) )) # Ptr  |-> retval_2)
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (head_init: (@list Z)) ,
  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= nv) ” 
  &&  “ ((Zlength (head_init)) = 0) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < 0)) -> ((Znth q head_init 0) = (-1))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  ((( &( "nn" ) )) # Int  |-> nv)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.seg head_p 0 0 head_init )
  **  (IntArray.undef_seg head_p 0 nv )
  **  (IntArray.undef_full to_p ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv (repeat_Z (0) (nv)) )
) \/
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z)  __default__Prod_Z_Z (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 100000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : ((Zlength (edges)) = (nv - 1 ))) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH11 : (Pre nv k_pre edges )) (PreH12 : (nn_pre = nv)) (PreH13 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH14 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH15 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
|--
  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < 0)) -> ((Znth q (@nil Z) 0) = (-1))) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ (GraphPre nn_pre edges ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z)  __default__Prod_Z_Z (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 100000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : ((Zlength (edges)) = (nv - 1 ))) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH11 : (Pre nv k_pre edges )) (PreH12 : (nn_pre = nv)) (PreH13 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH14 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH15 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
|--
  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z)  __default__Prod_Z_Z (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 100000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : ((Zlength (edges)) = (nv - 1 ))) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH11 : (Pre nv k_pre edges )) (PreH12 : (nn_pre = nv)) (PreH13 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH14 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH15 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
|--
  “ forall (q: Z) , (((0 <= q) /\ (q < 0)) -> ((Znth q (@nil Z) 0) = (-1))) ”
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z)  __default__Prod_Z_Z (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 100000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : ((Zlength (edges)) = (nv - 1 ))) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH11 : (Pre nv k_pre edges )) (PreH12 : (nn_pre = nv)) (PreH13 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH14 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH15 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
.

Definition solver_entail_wit_1_split_goal_4 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z)  __default__Prod_Z_Z (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 100000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : ((Zlength (edges)) = (nv - 1 ))) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH11 : (Pre nv k_pre edges )) (PreH12 : (nn_pre = nv)) (PreH13 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH14 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH15 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
|--
  “ (GraphPre nn_pre edges ) ”
.

Definition solver_entail_wit_1_split_goal_spatial := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z)  __default__Prod_Z_Z (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 100000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : ((Zlength (edges)) = (nv - 1 ))) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH11 : (Pre nv k_pre edges )) (PreH12 : (nn_pre = nv)) (PreH13 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH14 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH15 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
|--
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
.

Definition solver_entail_wit_2 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (head_init_2: (@list Z)) (i: Z)  __default__Prod_Z_Z (PreH1 : (i < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (GraphPre nv edges )) (PreH8 : (0 <= i)) (PreH9 : (i <= nv)) (PreH10 : ((Zlength (head_init_2)) = i)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < i)) -> ((Znth q head_init_2 0) = (-1)))) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.seg head_p_2 0 (i + 1 ) (app (head_init_2) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg head_p_2 (i + 1 ) nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.undef_full to_p_2 ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p_2 ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p_2 nv (repeat_Z (0) (nv)) )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (head_init: (@list Z)) ,
  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nv) ” 
  &&  “ ((Zlength (head_init)) = (i + 1 )) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (i + 1 ))) -> ((Znth q head_init 0) = (-1))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.seg head_p 0 (i + 1 ) head_init )
  **  (IntArray.undef_seg head_p (i + 1 ) nv )
  **  (IntArray.undef_full to_p ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv (repeat_Z (0) (nv)) )
) \/
(
forall (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (head_init_2: (@list Z)) (i: Z)  __default__Prod_Z_Z (PreH1 : (i < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (GraphPre nv edges )) (PreH8 : (0 <= i)) (PreH9 : (i <= nv)) (PreH10 : ((Zlength (head_init_2)) = i)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < i)) -> ((Znth q head_init_2 0) = (-1)))) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  TT && emp 
|--
  “ ((Zlength ((app (head_init_2) ((cons ((-1)) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (head_init_2: (@list Z)) (i: Z)  __default__Prod_Z_Z (PreH1 : (i < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (GraphPre nv edges )) (PreH8 : (0 <= i)) (PreH9 : (i <= nv)) (PreH10 : ((Zlength (head_init_2)) = i)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < i)) -> ((Znth q head_init_2 0) = (-1)))) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  ((Zlength ((app (head_init_2) ((cons ((-1)) ((@nil Z))))))) = (i + 1 ))
.

Definition solver_entail_wit_3 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (head_init: (@list Z)) (i: Z)  __default__Prod_Z_Z (PreH1 : (i >= nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (GraphPre nv edges )) (PreH8 : (0 <= i)) (PreH9 : (i <= nv)) (PreH10 : ((Zlength (head_init)) = i)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (nv - 1 ))) -> ((((((0 <= (Znth j_2 eu_data 0)) /\ ((Znth j_2 eu_data 0) < nv)) /\ (0 <= (Znth j_2 ev_data 0))) /\ ((Znth j_2 ev_data 0) < nv)) /\ ((Znth j_2 eu_data 0) = ((fst ((Znth j_2 edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j_2 ev_data 0) = ((snd ((Znth j_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.seg head_p_2 0 i head_init )
  **  (IntArray.undef_seg head_p_2 i nv )
  **  (IntArray.undef_full to_p_2 ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p_2 ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p_2 nv (repeat_Z (0) (nv)) )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (degree_data: (@list Z))  (next_done: (@list Z))  (to_done: (@list Z))  (head_data: (@list Z)) ,
  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (nv - 1 )) ” 
  &&  “ (0 = (2 * 0 )) ” 
  &&  “ ((Zlength (head_data)) = nv) ” 
  &&  “ ((Zlength (to_done)) = 0) ” 
  &&  “ ((Zlength (next_done)) = 0) ” 
  &&  “ ((Zlength (degree_data)) = nv) ” 
  &&  “ (AdjacencyBuildState nv edges 0 head_data to_done next_done ) ” 
  &&  “ (DegreePrefix nv edges 0 degree_data ) ” 
  &&  “ forall (index: Z) , (CurrentEdgeFresh edges index ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 0 to_done )
  **  (IntArray.undef_seg to_p 0 ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 0 next_done )
  **  (IntArray.undef_seg next_p 0 ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv degree_data )
) \/
(
forall (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (head_p_2: Z) (head_init: (@list Z)) (i: Z)  __default__Prod_Z_Z (PreH1 : (i >= nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (GraphPre nv edges )) (PreH8 : (0 <= i)) (PreH9 : (i <= nv)) (PreH10 : ((Zlength (head_init)) = i)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (nv - 1 ))) -> ((((((0 <= (Znth j_2 eu_data 0)) /\ ((Znth j_2 eu_data 0) < nv)) /\ (0 <= (Znth j_2 ev_data 0))) /\ ((Znth j_2 ev_data 0) < nv)) /\ ((Znth j_2 eu_data 0) = ((fst ((Znth j_2 edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j_2 ev_data 0) = ((snd ((Znth j_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.seg head_p_2 0 i head_init )
|--
  EX (head_data: (@list Z)) ,
  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (nv - 1 )) ” 
  &&  “ (0 = (2 * 0 )) ” 
  &&  “ ((Zlength (head_data)) = nv) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ ((Zlength ((repeat_Z (0) (nv)))) = nv) ” 
  &&  “ (AdjacencyBuildState nv edges 0 head_data (@nil Z) (@nil Z) ) ” 
  &&  “ (DegreePrefix nv edges 0 (repeat_Z (0) (nv)) ) ” 
  &&  “ forall (index: Z) , (CurrentEdgeFresh edges index ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (IntArray.full head_p_2 nv head_data )
).

Definition solver_entail_wit_4 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (degree_data_2: (@list Z)) (next_done_2: (@list Z)) (to_done_2: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data_2)) = nv)) (PreH11 : ((Zlength (to_done_2)) = ec)) (PreH12 : ((Zlength (next_done_2)) = ec)) (PreH13 : ((Zlength (degree_data_2)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data_2 to_done_2 next_done_2 )) (PreH15 : (DegreePrefix nv edges i degree_data_2 )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full deg_p_2 nv (replace_Znth ((Znth i ev_data 0)) (((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data_2 0) + 1 )) (degree_data_2)) 0) + 1 )) ((replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data_2 0) + 1 )) (degree_data_2)))) )
  **  (IntArray.full head_p_2 nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data_2)))) )
  **  (IntArray.seg next_p_2 0 ((ec + 1 ) + 1 ) (app ((app (next_done_2) ((cons ((Znth (Znth i eu_data 0) head_data_2 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data_2)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p_2 ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p_2 0 ((ec + 1 ) + 1 ) (app ((app (to_done_2) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p_2 ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (degree_data: (@list Z))  (next_done: (@list Z))  (to_done: (@list Z))  (head_data: (@list Z)) ,
  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (nv - 1 )) ” 
  &&  “ (((ec + 1 ) + 1 ) = (2 * (i + 1 ) )) ” 
  &&  “ ((Zlength (head_data)) = nv) ” 
  &&  “ ((Zlength (to_done)) = ((ec + 1 ) + 1 )) ” 
  &&  “ ((Zlength (next_done)) = ((ec + 1 ) + 1 )) ” 
  &&  “ ((Zlength (degree_data)) = nv) ” 
  &&  “ (AdjacencyBuildState nv edges (i + 1 ) head_data to_done next_done ) ” 
  &&  “ (DegreePrefix nv edges (i + 1 ) degree_data ) ” 
  &&  “ forall (index: Z) , (CurrentEdgeFresh edges index ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) to_done )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) next_done )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv degree_data )
) \/
(
forall (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (degree_data_2: (@list Z)) (next_done_2: (@list Z)) (to_done_2: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data_2)) = nv)) (PreH11 : ((Zlength (to_done_2)) = ec)) (PreH12 : ((Zlength (next_done_2)) = ec)) (PreH13 : ((Zlength (degree_data_2)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data_2 to_done_2 next_done_2 )) (PreH15 : (DegreePrefix nv edges i degree_data_2 )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  TT && emp 
|--
  “ (DegreePrefix nv edges (i + 1 ) (replace_Znth ((Znth i ev_data 0)) (((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data_2 0) + 1 )) (degree_data_2)) 0) + 1 )) ((replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data_2 0) + 1 )) (degree_data_2)))) ) ” 
  &&  “ (AdjacencyBuildState nv edges (i + 1 ) (replace_Znth ((Znth i ev_data 0)) (((2 * i ) + 1 )) ((replace_Znth ((Znth i eu_data 0)) ((2 * i )) (head_data_2)))) (app ((app (to_done_2) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) (app ((app (next_done_2) ((cons ((Znth (Znth i eu_data 0) head_data_2 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) ((2 * i )) (head_data_2)) 0)) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((replace_Znth ((Znth i ev_data 0)) (((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data_2 0) + 1 )) (degree_data_2)) 0) + 1 )) ((replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data_2 0) + 1 )) (degree_data_2)))))) = nv) ” 
  &&  “ ((Zlength ((app ((app (next_done_2) ((cons ((Znth (Znth i eu_data 0) head_data_2 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) ((2 * i )) (head_data_2)) 0)) ((@nil Z))))))) = (((2 * i ) + 1 ) + 1 )) ” 
  &&  “ ((Zlength ((app ((app (to_done_2) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))))) = (((2 * i ) + 1 ) + 1 )) ” 
  &&  “ ((Zlength ((replace_Znth ((Znth i ev_data 0)) (((2 * i ) + 1 )) ((replace_Znth ((Znth i eu_data 0)) ((2 * i )) (head_data_2)))))) = nv) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (degree_data_2: (@list Z)) (next_done_2: (@list Z)) (to_done_2: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data_2)) = nv)) (PreH11 : ((Zlength (to_done_2)) = ec)) (PreH12 : ((Zlength (next_done_2)) = ec)) (PreH13 : ((Zlength (degree_data_2)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data_2 to_done_2 next_done_2 )) (PreH15 : (DegreePrefix nv edges i degree_data_2 )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (DegreePrefix nv edges (i + 1 ) (replace_Znth ((Znth i ev_data 0)) (((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data_2 0) + 1 )) (degree_data_2)) 0) + 1 )) ((replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data_2 0) + 1 )) (degree_data_2)))) )
.

Definition solver_entail_wit_4_split_goal_2 := 
forall (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (degree_data_2: (@list Z)) (next_done_2: (@list Z)) (to_done_2: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data_2)) = nv)) (PreH11 : ((Zlength (to_done_2)) = ec)) (PreH12 : ((Zlength (next_done_2)) = ec)) (PreH13 : ((Zlength (degree_data_2)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data_2 to_done_2 next_done_2 )) (PreH15 : (DegreePrefix nv edges i degree_data_2 )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (AdjacencyBuildState nv edges (i + 1 ) (replace_Znth ((Znth i ev_data 0)) (((2 * i ) + 1 )) ((replace_Znth ((Znth i eu_data 0)) ((2 * i )) (head_data_2)))) (app ((app (to_done_2) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) (app ((app (next_done_2) ((cons ((Znth (Znth i eu_data 0) head_data_2 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) ((2 * i )) (head_data_2)) 0)) ((@nil Z))))) )
.

Definition solver_entail_wit_4_split_goal_3 := 
forall (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (degree_data_2: (@list Z)) (next_done_2: (@list Z)) (to_done_2: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data_2)) = nv)) (PreH11 : ((Zlength (to_done_2)) = ec)) (PreH12 : ((Zlength (next_done_2)) = ec)) (PreH13 : ((Zlength (degree_data_2)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data_2 to_done_2 next_done_2 )) (PreH15 : (DegreePrefix nv edges i degree_data_2 )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  ((Zlength ((replace_Znth ((Znth i ev_data 0)) (((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data_2 0) + 1 )) (degree_data_2)) 0) + 1 )) ((replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data_2 0) + 1 )) (degree_data_2)))))) = nv)
.

Definition solver_entail_wit_4_split_goal_4 := 
forall (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (degree_data_2: (@list Z)) (next_done_2: (@list Z)) (to_done_2: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data_2)) = nv)) (PreH11 : ((Zlength (to_done_2)) = ec)) (PreH12 : ((Zlength (next_done_2)) = ec)) (PreH13 : ((Zlength (degree_data_2)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data_2 to_done_2 next_done_2 )) (PreH15 : (DegreePrefix nv edges i degree_data_2 )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  ((Zlength ((app ((app (next_done_2) ((cons ((Znth (Znth i eu_data 0) head_data_2 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) ((2 * i )) (head_data_2)) 0)) ((@nil Z))))))) = (((2 * i ) + 1 ) + 1 ))
.

Definition solver_entail_wit_4_split_goal_5 := 
forall (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (degree_data_2: (@list Z)) (next_done_2: (@list Z)) (to_done_2: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data_2)) = nv)) (PreH11 : ((Zlength (to_done_2)) = ec)) (PreH12 : ((Zlength (next_done_2)) = ec)) (PreH13 : ((Zlength (degree_data_2)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data_2 to_done_2 next_done_2 )) (PreH15 : (DegreePrefix nv edges i degree_data_2 )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  ((Zlength ((app ((app (to_done_2) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))))) = (((2 * i ) + 1 ) + 1 ))
.

Definition solver_entail_wit_4_split_goal_6 := 
forall (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (degree_data_2: (@list Z)) (next_done_2: (@list Z)) (to_done_2: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data_2)) = nv)) (PreH11 : ((Zlength (to_done_2)) = ec)) (PreH12 : ((Zlength (next_done_2)) = ec)) (PreH13 : ((Zlength (degree_data_2)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data_2 to_done_2 next_done_2 )) (PreH15 : (DegreePrefix nv edges i degree_data_2 )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  ((Zlength ((replace_Znth ((Znth i ev_data 0)) (((2 * i ) + 1 )) ((replace_Znth ((Znth i eu_data 0)) ((2 * i )) (head_data_2)))))) = nv)
.

Definition solver_entail_wit_5 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (degree_data_2: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) >= nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data_2)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data_2)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data_2 to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data_2 )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.seg to_p_2 0 ec to_done )
  **  (IntArray.undef_seg to_p_2 ec ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p_2 0 ec next_done )
  **  (IntArray.undef_seg next_p_2 ec ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p_2 nv degree_data_2 )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (degree_data: (@list Z))  (head_data: (@list Z))  (to_data: (@list Z))  (next_data: (@list Z)) ,
  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
) \/
(
forall (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (next_p_2: Z) (to_p_2: Z) (degree_data_2: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data_2: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) >= nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data_2)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data_2)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data_2 to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data_2 )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.seg to_p_2 0 ec to_done )
  **  (IntArray.seg next_p_2 0 ec next_done )
|--
  EX (to_data: (@list Z))  (next_data: (@list Z)) ,
  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data_2 to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data_2 ) ”
  &&  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data )
).

Definition solver_entail_wit_6 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (head_p_2: Z) (to_p_2: Z) (next_p_2: Z) (deg_p_2: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (degree_data_2: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (retval_3: Z) (PreH1 : (BFSResult nv edges 0 parent_data dist_data retval_3 )) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (ec = ((2 * nv ) - 2 ))) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 100000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : (Pre nv k_pre edges )) (PreH10 : (GraphPre nv edges )) (PreH11 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH12 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) ,
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full retval nv parent_data )
  **  (IntArray.full retval_2 nv dist_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.full deg_p_2 nv degree_data_2 )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (degree_data: (@list Z))  (head_data: (@list Z))  (to_data: (@list Z))  (next_data: (@list Z))  (first_parent: (@list Z))  (first_dist: (@list Z)) ,
  “ (BFSResult nv edges 0 first_parent first_dist retval_3 ) ” 
  &&  “ (1 = 1) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full_shape retval nv )
  **  (IntArray.full_shape retval_2 nv )
) \/
(
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (degree_data_2: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (retval_3: Z) (PreH1 : (BFSResult nv edges 0 parent_data dist_data retval_3 )) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (ec = ((2 * nv ) - 2 ))) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 100000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : (Pre nv k_pre edges )) (PreH10 : (GraphPre nv edges )) (PreH11 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH12 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) ,
  (IntArray.full retval nv parent_data )
  **  (IntArray.full retval_2 nv dist_data )
|--
  EX (first_parent: (@list Z))  (first_dist: (@list Z)) ,
  “ (BFSResult nv edges 0 first_parent first_dist retval_3 ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data_2 ) ”
  &&  (IntArray.full_shape retval nv )
  **  (IntArray.full_shape retval_2 nv )
).

Definition solver_entail_wit_7 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (head_p_2: Z) (to_p_2: Z) (next_p_2: Z) (deg_p_2: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (degree_data_2: (@list Z)) (a: Z) (ok: Z) (ec: Z) (p: Z) (d: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (retval: Z) (PreH1 : (BFSResult nv edges a parent_data dist_data retval )) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (ok = 1)) (PreH4 : (ec = ((2 * nv ) - 2 ))) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 100000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : (GraphPre nv edges )) (PreH10 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH11 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) ,
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full p nv parent_data )
  **  (IntArray.full d nv dist_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.full deg_p_2 nv degree_data_2 )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (degree_data: (@list Z))  (head_data: (@list Z))  (to_data: (@list Z))  (next_data: (@list Z))  (second_parent: (@list Z))  (second_dist: (@list Z))  (first_parent: (@list Z))  (first_dist: (@list Z)) ,
  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist retval ) ” 
  &&  “ (0 <= a) ” 
  &&  “ (a < nv) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < nv) ” 
  &&  “ (ok = 1) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv second_parent )
  **  (IntArray.full d nv second_dist )
) \/
(
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (degree_data_2: (@list Z)) (a: Z) (ok: Z) (ec: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (retval: Z) (PreH1 : (BFSResult nv edges a parent_data dist_data retval )) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (ok = 1)) (PreH4 : (ec = ((2 * nv ) - 2 ))) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 100000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : (GraphPre nv edges )) (PreH10 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH11 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) ,
  TT && emp 
|--
  “ (retval < nv) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (a < nv) ” 
  &&  “ (0 <= a) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 := 
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (degree_data_2: (@list Z)) (a: Z) (ok: Z) (ec: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (retval: Z) (PreH1 : (BFSResult nv edges a parent_data dist_data retval )) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (ok = 1)) (PreH4 : (ec = ((2 * nv ) - 2 ))) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 100000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : (GraphPre nv edges )) (PreH10 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH11 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) ,
  (retval < nv)
.

Definition solver_entail_wit_7_split_goal_2 := 
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (degree_data_2: (@list Z)) (a: Z) (ok: Z) (ec: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (retval: Z) (PreH1 : (BFSResult nv edges a parent_data dist_data retval )) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (ok = 1)) (PreH4 : (ec = ((2 * nv ) - 2 ))) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 100000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : (GraphPre nv edges )) (PreH10 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH11 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) ,
  (0 <= retval)
.

Definition solver_entail_wit_7_split_goal_3 := 
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (degree_data_2: (@list Z)) (a: Z) (ok: Z) (ec: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (retval: Z) (PreH1 : (BFSResult nv edges a parent_data dist_data retval )) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (ok = 1)) (PreH4 : (ec = ((2 * nv ) - 2 ))) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 100000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : (GraphPre nv edges )) (PreH10 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH11 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) ,
  (a < nv)
.

Definition solver_entail_wit_7_split_goal_4 := 
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (degree_data_2: (@list Z)) (a: Z) (ok: Z) (ec: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (retval: Z) (PreH1 : (BFSResult nv edges a parent_data dist_data retval )) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (ok = 1)) (PreH4 : (ec = ((2 * nv ) - 2 ))) (PreH5 : (1 <= nv)) (PreH6 : (nv <= 100000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : (GraphPre nv edges )) (PreH10 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH11 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) ,
  (0 <= a)
.

Definition solver_entail_wit_8_1 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (head_p_2: Z) (to_p_2: Z) (next_p_2: Z) (deg_p_2: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (degree_data_2: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (p: Z) (d: Z) (PreH1 : ((Znth b second_dist_2 0) <> (2 * k_pre ))) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH4 : (0 <= a)) (PreH5 : (a < nv)) (PreH6 : (0 <= b)) (PreH7 : (b < nv)) (PreH8 : (ok = 1)) (PreH9 : (ec = ((2 * nv ) - 2 ))) (PreH10 : (1 <= nv)) (PreH11 : (nv <= 100000)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (GraphPre nv edges )) (PreH15 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH16 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) ,
  (IntArray.full d nv second_dist_2 )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full deg_p_2 nv degree_data_2 )
  **  (IntArray.full p nv second_parent_2 )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (degree_data: (@list Z))  (head_data: (@list Z))  (to_data: (@list Z))  (next_data: (@list Z))  (second_parent: (@list Z))  (second_dist: (@list Z))  (first_parent: (@list Z))  (first_dist: (@list Z)) ,
  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (DiameterDecision k_pre second_dist b 0 ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b < nv) ” 
  &&  “ (AncestorAfter second_parent b 0 b ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv second_parent )
  **  (IntArray.full d nv second_dist )
) \/
(
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (degree_data_2: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (PreH1 : ((Znth b second_dist_2 0) <> (2 * k_pre ))) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH4 : (0 <= a)) (PreH5 : (a < nv)) (PreH6 : (0 <= b)) (PreH7 : (b < nv)) (PreH8 : (ok = 1)) (PreH9 : (ec = ((2 * nv ) - 2 ))) (PreH10 : (1 <= nv)) (PreH11 : (nv <= 100000)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (GraphPre nv edges )) (PreH15 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH16 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) ,
  TT && emp 
|--
  “ (AncestorAfter second_parent_2 b 0 b ) ” 
  &&  “ (DiameterDecision k_pre second_dist_2 b 0 ) ”
  &&  emp
).

Definition solver_entail_wit_8_1_split_goal_1 := 
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (degree_data_2: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (PreH1 : ((Znth b second_dist_2 0) <> (2 * k_pre ))) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH4 : (0 <= a)) (PreH5 : (a < nv)) (PreH6 : (0 <= b)) (PreH7 : (b < nv)) (PreH8 : (ok = 1)) (PreH9 : (ec = ((2 * nv ) - 2 ))) (PreH10 : (1 <= nv)) (PreH11 : (nv <= 100000)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (GraphPre nv edges )) (PreH15 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH16 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) ,
  (AncestorAfter second_parent_2 b 0 b )
.

Definition solver_entail_wit_8_1_split_goal_2 := 
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (degree_data_2: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (PreH1 : ((Znth b second_dist_2 0) <> (2 * k_pre ))) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH4 : (0 <= a)) (PreH5 : (a < nv)) (PreH6 : (0 <= b)) (PreH7 : (b < nv)) (PreH8 : (ok = 1)) (PreH9 : (ec = ((2 * nv ) - 2 ))) (PreH10 : (1 <= nv)) (PreH11 : (nv <= 100000)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (GraphPre nv edges )) (PreH15 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH16 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) ,
  (DiameterDecision k_pre second_dist_2 b 0 )
.

Definition solver_entail_wit_8_2 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (head_p_2: Z) (to_p_2: Z) (next_p_2: Z) (deg_p_2: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (degree_data_2: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (p: Z) (d: Z) (PreH1 : ((Znth b second_dist_2 0) = (2 * k_pre ))) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH4 : (0 <= a)) (PreH5 : (a < nv)) (PreH6 : (0 <= b)) (PreH7 : (b < nv)) (PreH8 : (ok = 1)) (PreH9 : (ec = ((2 * nv ) - 2 ))) (PreH10 : (1 <= nv)) (PreH11 : (nv <= 100000)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (GraphPre nv edges )) (PreH15 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH16 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) ,
  (IntArray.full d nv second_dist_2 )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full deg_p_2 nv degree_data_2 )
  **  (IntArray.full p nv second_parent_2 )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (degree_data: (@list Z))  (head_data: (@list Z))  (to_data: (@list Z))  (next_data: (@list Z))  (second_parent: (@list Z))  (second_dist: (@list Z))  (first_parent: (@list Z))  (first_dist: (@list Z)) ,
  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (DiameterDecision k_pre second_dist b ok ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b < nv) ” 
  &&  “ (AncestorAfter second_parent b 0 b ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv second_parent )
  **  (IntArray.full d nv second_dist )
) \/
(
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (degree_data_2: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (PreH1 : ((Znth b second_dist_2 0) = (2 * k_pre ))) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH4 : (0 <= a)) (PreH5 : (a < nv)) (PreH6 : (0 <= b)) (PreH7 : (b < nv)) (PreH8 : (ok = 1)) (PreH9 : (ec = ((2 * nv ) - 2 ))) (PreH10 : (1 <= nv)) (PreH11 : (nv <= 100000)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (GraphPre nv edges )) (PreH15 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH16 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) ,
  TT && emp 
|--
  “ (AncestorAfter second_parent_2 b 0 b ) ” 
  &&  “ (DiameterDecision k_pre second_dist_2 b 1 ) ”
  &&  emp
).

Definition solver_entail_wit_8_2_split_goal_1 := 
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (degree_data_2: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (PreH1 : ((Znth b second_dist_2 0) = (2 * k_pre ))) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH4 : (0 <= a)) (PreH5 : (a < nv)) (PreH6 : (0 <= b)) (PreH7 : (b < nv)) (PreH8 : (ok = 1)) (PreH9 : (ec = ((2 * nv ) - 2 ))) (PreH10 : (1 <= nv)) (PreH11 : (nv <= 100000)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (GraphPre nv edges )) (PreH15 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH16 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) ,
  (AncestorAfter second_parent_2 b 0 b )
.

Definition solver_entail_wit_8_2_split_goal_2 := 
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (degree_data_2: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (PreH1 : ((Znth b second_dist_2 0) = (2 * k_pre ))) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH4 : (0 <= a)) (PreH5 : (a < nv)) (PreH6 : (0 <= b)) (PreH7 : (b < nv)) (PreH8 : (ok = 1)) (PreH9 : (ec = ((2 * nv ) - 2 ))) (PreH10 : (1 <= nv)) (PreH11 : (nv <= 100000)) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (GraphPre nv edges )) (PreH15 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH16 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) ,
  (DiameterDecision k_pre second_dist_2 b 1 )
.

Definition solver_entail_wit_9 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (center: Z) (i: Z) (ok: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : (i < k_pre)) (PreH2 : (ok <> 0)) (PreH3 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH4 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH5 : (GraphPre nv edges )) (PreH6 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH7 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH8 : (ec = ((2 * nv ) - 2 ))) (PreH9 : (1 <= nv)) (PreH10 : (nv <= 100000)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (DiameterDecision k_pre second_dist_2 b ok )) (PreH14 : (0 <= i)) (PreH15 : (i <= k_pre)) (PreH16 : (0 <= center)) (PreH17 : (center < nv)) (PreH18 : (AncestorAfter second_parent_2 b i center )) ,
  (IntArray.full p nv second_parent_2 )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full deg_p_2 nv degree_data_2 )
  **  (IntArray.full d nv second_dist_2 )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (degree_data: (@list Z))  (head_data: (@list Z))  (to_data: (@list Z))  (next_data: (@list Z))  (second_parent: (@list Z))  (second_dist: (@list Z))  (first_parent: (@list Z))  (first_dist: (@list Z)) ,
  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (DiameterDecision k_pre second_dist b ok ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= k_pre) ” 
  &&  “ (0 <= (Znth center second_parent_2 0)) ” 
  &&  “ ((Znth center second_parent_2 0) < nv) ” 
  &&  “ (AncestorAfter second_parent b (i + 1 ) (Znth center second_parent_2 0) ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv second_parent )
  **  (IntArray.full d nv second_dist )
) \/
(
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (center: Z) (i: Z) (ok: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : (i < k_pre)) (PreH2 : (ok <> 0)) (PreH3 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH4 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH5 : (GraphPre nv edges )) (PreH6 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH7 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH8 : (ec = ((2 * nv ) - 2 ))) (PreH9 : (1 <= nv)) (PreH10 : (nv <= 100000)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (DiameterDecision k_pre second_dist_2 b ok )) (PreH14 : (0 <= i)) (PreH15 : (i <= k_pre)) (PreH16 : (0 <= center)) (PreH17 : (center < nv)) (PreH18 : (AncestorAfter second_parent_2 b i center )) ,
  TT && emp 
|--
  “ (AncestorAfter second_parent_2 b (i + 1 ) (Znth center second_parent_2 0) ) ” 
  &&  “ ((Znth center second_parent_2 0) < nv) ” 
  &&  “ (0 <= (Znth center second_parent_2 0)) ”
  &&  emp
).

Definition solver_entail_wit_9_split_goal_1 := 
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (center: Z) (i: Z) (ok: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : (i < k_pre)) (PreH2 : (ok <> 0)) (PreH3 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH4 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH5 : (GraphPre nv edges )) (PreH6 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH7 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH8 : (ec = ((2 * nv ) - 2 ))) (PreH9 : (1 <= nv)) (PreH10 : (nv <= 100000)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (DiameterDecision k_pre second_dist_2 b ok )) (PreH14 : (0 <= i)) (PreH15 : (i <= k_pre)) (PreH16 : (0 <= center)) (PreH17 : (center < nv)) (PreH18 : (AncestorAfter second_parent_2 b i center )) ,
  (AncestorAfter second_parent_2 b (i + 1 ) (Znth center second_parent_2 0) )
.

Definition solver_entail_wit_9_split_goal_2 := 
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (center: Z) (i: Z) (ok: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : (i < k_pre)) (PreH2 : (ok <> 0)) (PreH3 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH4 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH5 : (GraphPre nv edges )) (PreH6 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH7 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH8 : (ec = ((2 * nv ) - 2 ))) (PreH9 : (1 <= nv)) (PreH10 : (nv <= 100000)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (DiameterDecision k_pre second_dist_2 b ok )) (PreH14 : (0 <= i)) (PreH15 : (i <= k_pre)) (PreH16 : (0 <= center)) (PreH17 : (center < nv)) (PreH18 : (AncestorAfter second_parent_2 b i center )) ,
  ((Znth center second_parent_2 0) < nv)
.

Definition solver_entail_wit_9_split_goal_3 := 
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (center: Z) (i: Z) (ok: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : (i < k_pre)) (PreH2 : (ok <> 0)) (PreH3 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH4 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH5 : (GraphPre nv edges )) (PreH6 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH7 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH8 : (ec = ((2 * nv ) - 2 ))) (PreH9 : (1 <= nv)) (PreH10 : (nv <= 100000)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (DiameterDecision k_pre second_dist_2 b ok )) (PreH14 : (0 <= i)) (PreH15 : (i <= k_pre)) (PreH16 : (0 <= center)) (PreH17 : (center < nv)) (PreH18 : (AncestorAfter second_parent_2 b i center )) ,
  (0 <= (Znth center second_parent_2 0))
.

Definition solver_entail_wit_10_1 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (i: Z) (ok: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : (ok = 0)) (PreH2 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH3 : (BFSResult nv edges a second_parent second_dist b )) (PreH4 : (GraphPre nv edges )) (PreH5 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH6 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH7 : (ec = ((2 * nv ) - 2 ))) (PreH8 : (1 <= nv)) (PreH9 : (nv <= 100000)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 1000000000)) (PreH12 : (DiameterDecision k_pre second_dist b ok )) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= center)) (PreH16 : (center < nv)) (PreH17 : (AncestorAfter second_parent b i center )) (PreH18 : (ok = 0)) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv second_parent )
  **  (IntArray.full d nv second_dist )
|--
  “ (ok = 0) ” 
  &&  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (DiameterDecision k_pre second_dist b ok ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= k_pre) ” 
  &&  “ (0 <= center) ” 
  &&  “ (center < nv) ” 
  &&  “ (AncestorAfter second_parent b i center ) ” 
  &&  “ (ok = 0) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv second_parent )
  **  (IntArray.full d nv second_dist )
.

Definition solver_entail_wit_10_2 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (i: Z) (ok: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : (i >= k_pre)) (PreH2 : (ok <> 0)) (PreH3 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH4 : (BFSResult nv edges a second_parent second_dist b )) (PreH5 : (GraphPre nv edges )) (PreH6 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH7 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH8 : (ec = ((2 * nv ) - 2 ))) (PreH9 : (1 <= nv)) (PreH10 : (nv <= 100000)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (DiameterDecision k_pre second_dist b ok )) (PreH14 : (0 <= i)) (PreH15 : (i <= k_pre)) (PreH16 : (0 <= center)) (PreH17 : (center < nv)) (PreH18 : (AncestorAfter second_parent b i center )) (PreH19 : (ok = 0)) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv second_parent )
  **  (IntArray.full d nv second_dist )
|--
  “ (ok = 0) ” 
  &&  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (DiameterDecision k_pre second_dist b ok ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= k_pre) ” 
  &&  “ (0 <= center) ” 
  &&  “ (center < nv) ” 
  &&  “ (AncestorAfter second_parent b i center ) ” 
  &&  “ (ok = 0) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv second_parent )
  **  (IntArray.full d nv second_dist )
.

Definition solver_entail_wit_11_1 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (i: Z) (ok: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : (ok = 0)) (PreH2 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH3 : (BFSResult nv edges a second_parent second_dist b )) (PreH4 : (GraphPre nv edges )) (PreH5 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH6 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH7 : (ec = ((2 * nv ) - 2 ))) (PreH8 : (1 <= nv)) (PreH9 : (nv <= 100000)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 1000000000)) (PreH12 : (DiameterDecision k_pre second_dist b ok )) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= center)) (PreH16 : (center < nv)) (PreH17 : (AncestorAfter second_parent b i center )) (PreH18 : (ok <> 0)) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv second_parent )
  **  (IntArray.full d nv second_dist )
|--
  “ (i >= k_pre) ” 
  &&  “ (ok <> 0) ” 
  &&  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (DiameterDecision k_pre second_dist b ok ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= k_pre) ” 
  &&  “ (0 <= center) ” 
  &&  “ (center < nv) ” 
  &&  “ (AncestorAfter second_parent b i center ) ” 
  &&  “ (ok <> 0) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv second_parent )
  **  (IntArray.full d nv second_dist )
.

Definition solver_entail_wit_11_2 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (i: Z) (ok: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : (i >= k_pre)) (PreH2 : (ok <> 0)) (PreH3 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH4 : (BFSResult nv edges a second_parent second_dist b )) (PreH5 : (GraphPre nv edges )) (PreH6 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH7 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH8 : (ec = ((2 * nv ) - 2 ))) (PreH9 : (1 <= nv)) (PreH10 : (nv <= 100000)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (DiameterDecision k_pre second_dist b ok )) (PreH14 : (0 <= i)) (PreH15 : (i <= k_pre)) (PreH16 : (0 <= center)) (PreH17 : (center < nv)) (PreH18 : (AncestorAfter second_parent b i center )) (PreH19 : (ok <> 0)) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv second_parent )
  **  (IntArray.full d nv second_dist )
|--
  “ (i >= k_pre) ” 
  &&  “ (ok <> 0) ” 
  &&  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (DiameterDecision k_pre second_dist b ok ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= k_pre) ” 
  &&  “ (0 <= center) ” 
  &&  “ (center < nv) ” 
  &&  “ (AncestorAfter second_parent b i center ) ” 
  &&  “ (ok <> 0) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv second_parent )
  **  (IntArray.full d nv second_dist )
.

Definition solver_entail_wit_12 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (center: Z) (i: Z) (ok: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : (i >= k_pre)) (PreH2 : (ok <> 0)) (PreH3 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH4 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH5 : (GraphPre nv edges )) (PreH6 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH7 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH8 : (ec = ((2 * nv ) - 2 ))) (PreH9 : (1 <= nv)) (PreH10 : (nv <= 100000)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (DiameterDecision k_pre second_dist_2 b ok )) (PreH14 : (0 <= i)) (PreH15 : (i <= k_pre)) (PreH16 : (0 <= center)) (PreH17 : (center < nv)) (PreH18 : (AncestorAfter second_parent_2 b i center )) (PreH19 : (ok <> 0)) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full deg_p_2 nv degree_data_2 )
  **  (IntArray.full p nv second_parent_2 )
  **  (IntArray.full d nv second_dist_2 )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (degree_data: (@list Z))  (head_data: (@list Z))  (to_data: (@list Z))  (next_data: (@list Z))  (second_parent: (@list Z))  (second_dist: (@list Z))  (first_parent: (@list Z))  (first_dist: (@list Z)) ,
  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ok = 1) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= center) ” 
  &&  “ (center < nv) ” 
  &&  “ (AncestorAfter second_parent b k_pre center ) ” 
  &&  “ ((Znth b second_dist 0) = (2 * k_pre )) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full_shape p nv )
  **  (IntArray.full_shape d nv )
) \/
(
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (center: Z) (i: Z) (ok: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : (i >= k_pre)) (PreH2 : (ok <> 0)) (PreH3 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH4 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH5 : (GraphPre nv edges )) (PreH6 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH7 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH8 : (ec = ((2 * nv ) - 2 ))) (PreH9 : (1 <= nv)) (PreH10 : (nv <= 100000)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (DiameterDecision k_pre second_dist_2 b ok )) (PreH14 : (0 <= i)) (PreH15 : (i <= k_pre)) (PreH16 : (0 <= center)) (PreH17 : (center < nv)) (PreH18 : (AncestorAfter second_parent_2 b i center )) (PreH19 : (ok <> 0)) ,
  (IntArray.full p nv second_parent_2 )
  **  (IntArray.full d nv second_dist_2 )
|--
  EX (second_parent: (@list Z))  (second_dist: (@list Z))  (first_parent: (@list Z))  (first_dist: (@list Z)) ,
  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data_2 ) ” 
  &&  “ (ok = 1) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= center) ” 
  &&  “ (center < nv) ” 
  &&  “ (AncestorAfter second_parent b k_pre center ) ” 
  &&  “ ((Znth b second_dist 0) = (2 * k_pre )) ”
  &&  (IntArray.full_shape p nv )
  **  (IntArray.full_shape d nv )
).

Definition solver_entail_wit_13_1 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (head_p_2: Z) (to_p_2: Z) (next_p_2: Z) (deg_p_2: Z) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (degree_data_2: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (center: Z) (p: Z) (d: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (retval: Z) (PreH1 : (BFSResult nv edges center parent_data dist_data retval )) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH4 : (GraphPre nv edges )) (PreH5 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH6 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH7 : (ok = 1)) (PreH8 : (1 <= nv)) (PreH9 : (nv <= 100000)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 1000000000)) (PreH12 : (ec = ((2 * nv ) - 2 ))) (PreH13 : (0 <= center)) (PreH14 : (center < nv)) (PreH15 : (AncestorAfter second_parent_2 b k_pre center )) (PreH16 : ((Znth b second_dist_2 0) = (2 * k_pre ))) ,
  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full p nv parent_data )
  **  (IntArray.full d nv dist_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.full deg_p_2 nv degree_data_2 )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (center_parent: (@list Z))  (center_dist: (@list Z))  (degree_data: (@list Z))  (head_data: (@list Z))  (to_data: (@list Z))  (next_data: (@list Z))  (second_parent: (@list Z))  (second_dist: (@list Z))  (first_parent: (@list Z))  (first_dist: (@list Z)) ,
  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data 0 ok ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
) \/
(
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (degree_data_2: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (center: Z) (parent_data: (@list Z)) (dist_data: (@list Z)) (retval: Z) (PreH1 : (BFSResult nv edges center parent_data dist_data retval )) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH4 : (GraphPre nv edges )) (PreH5 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH6 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH7 : (ok = 1)) (PreH8 : (1 <= nv)) (PreH9 : (nv <= 100000)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 1000000000)) (PreH12 : (ec = ((2 * nv ) - 2 ))) (PreH13 : (0 <= center)) (PreH14 : (center < nv)) (PreH15 : (AncestorAfter second_parent_2 b k_pre center )) (PreH16 : ((Znth b second_dist_2 0) = (2 * k_pre ))) ,
  TT && emp 
|--
  EX (second_parent: (@list Z))  (second_dist: (@list Z)) ,
  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center parent_data dist_data degree_data_2 0 1 ) ”
  &&  emp
).

Definition solver_entail_wit_13_2 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (center: Z) (i: Z) (ok: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : (ok = 0)) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH4 : (GraphPre nv edges )) (PreH5 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH6 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH7 : (ec = ((2 * nv ) - 2 ))) (PreH8 : (1 <= nv)) (PreH9 : (nv <= 100000)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 1000000000)) (PreH12 : (DiameterDecision k_pre second_dist_2 b ok )) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= center)) (PreH16 : (center < nv)) (PreH17 : (AncestorAfter second_parent_2 b i center )) (PreH18 : (ok = 0)) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full deg_p_2 nv degree_data_2 )
  **  (IntArray.full p nv second_parent_2 )
  **  (IntArray.full d nv second_dist_2 )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (center_parent: (@list Z))  (center_dist: (@list Z))  (degree_data: (@list Z))  (head_data: (@list Z))  (to_data: (@list Z))  (next_data: (@list Z))  (second_parent: (@list Z))  (second_dist: (@list Z))  (first_parent: (@list Z))  (first_dist: (@list Z)) ,
  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data 0 ok ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
) \/
(
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (center: Z) (i: Z) (ok: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : (ok = 0)) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH4 : (GraphPre nv edges )) (PreH5 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH6 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH7 : (ec = ((2 * nv ) - 2 ))) (PreH8 : (1 <= nv)) (PreH9 : (nv <= 100000)) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 1000000000)) (PreH12 : (DiameterDecision k_pre second_dist_2 b ok )) (PreH13 : (0 <= i)) (PreH14 : (i <= k_pre)) (PreH15 : (0 <= center)) (PreH16 : (center < nv)) (PreH17 : (AncestorAfter second_parent_2 b i center )) (PreH18 : (ok = 0)) ,
  TT && emp 
|--
  EX (second_parent: (@list Z))  (second_dist: (@list Z)) ,
  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center second_parent_2 second_dist_2 degree_data_2 0 0 ) ”
  &&  emp
).

Definition solver_entail_wit_14_1 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (center: Z) (center_parent_2: (@list Z)) (center_dist_2: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : ((Znth v degree_data_2 0) <> 1)) (PreH2 : ((Znth v center_dist_2 0) = k_pre)) (PreH3 : ((Znth v center_dist_2 0) <= k_pre)) (PreH4 : (v < nv)) (PreH5 : (ok <> 0)) (PreH6 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH7 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH8 : (GraphPre nv edges )) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 1000000000)) (PreH11 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH12 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH13 : (ec = ((2 * nv ) - 2 ))) (PreH14 : (0 <= v)) (PreH15 : (v <= nv)) (PreH16 : (SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center center_parent_2 center_dist_2 degree_data_2 v ok )) ,
  (IntArray.full deg_p_2 nv degree_data_2 )
  **  (IntArray.full d nv center_dist_2 )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full p nv center_parent_2 )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (center_parent: (@list Z))  (center_dist: (@list Z))  (degree_data: (@list Z))  (head_data: (@list Z))  (to_data: (@list Z))  (next_data: (@list Z))  (second_parent: (@list Z))  (second_dist: (@list Z))  (first_parent: (@list Z))  (first_dist: (@list Z)) ,
  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data (v + 1 ) 0 ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
) \/
(
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (center: Z) (center_parent_2: (@list Z)) (center_dist_2: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : ((Znth v degree_data_2 0) <> 1)) (PreH2 : ((Znth v center_dist_2 0) = k_pre)) (PreH3 : ((Znth v center_dist_2 0) <= k_pre)) (PreH4 : (v < nv)) (PreH5 : (ok <> 0)) (PreH6 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH7 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH8 : (GraphPre nv edges )) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 1000000000)) (PreH11 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH12 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH13 : (ec = ((2 * nv ) - 2 ))) (PreH14 : (0 <= v)) (PreH15 : (v <= nv)) (PreH16 : (SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center center_parent_2 center_dist_2 degree_data_2 v ok )) ,
  TT && emp 
|--
  EX (second_parent: (@list Z))  (second_dist: (@list Z)) ,
  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (0 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= nv) ” 
  &&  “ (SolverDecision nv (Znth v center_dist_2 0) edges second_parent second_dist b center center_parent_2 center_dist_2 degree_data_2 (v + 1 ) 0 ) ”
  &&  emp
).

Definition solver_entail_wit_14_2 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (center: Z) (center_parent_2: (@list Z)) (center_dist_2: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : ((Znth v center_dist_2 0) > k_pre)) (PreH2 : (v < nv)) (PreH3 : (ok <> 0)) (PreH4 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH5 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH6 : (GraphPre nv edges )) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH10 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH11 : (ec = ((2 * nv ) - 2 ))) (PreH12 : (0 <= v)) (PreH13 : (v <= nv)) (PreH14 : (SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center center_parent_2 center_dist_2 degree_data_2 v ok )) ,
  (IntArray.full d nv center_dist_2 )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full deg_p_2 nv degree_data_2 )
  **  (IntArray.full p nv center_parent_2 )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (center_parent: (@list Z))  (center_dist: (@list Z))  (degree_data: (@list Z))  (head_data: (@list Z))  (to_data: (@list Z))  (next_data: (@list Z))  (second_parent: (@list Z))  (second_dist: (@list Z))  (first_parent: (@list Z))  (first_dist: (@list Z)) ,
  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data (v + 1 ) 0 ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
) \/
(
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (center: Z) (center_parent_2: (@list Z)) (center_dist_2: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : ((Znth v center_dist_2 0) > k_pre)) (PreH2 : (v < nv)) (PreH3 : (ok <> 0)) (PreH4 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH5 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH6 : (GraphPre nv edges )) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH10 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH11 : (ec = ((2 * nv ) - 2 ))) (PreH12 : (0 <= v)) (PreH13 : (v <= nv)) (PreH14 : (SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center center_parent_2 center_dist_2 degree_data_2 v ok )) ,
  TT && emp 
|--
  EX (second_parent: (@list Z))  (second_dist: (@list Z)) ,
  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (0 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent_2 center_dist_2 degree_data_2 (v + 1 ) 0 ) ”
  &&  emp
).

Definition solver_entail_wit_14_3 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (center: Z) (center_parent_2: (@list Z)) (center_dist_2: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : ((Znth v degree_data_2 0) < 3)) (PreH2 : (v = center)) (PreH3 : ((Znth v center_dist_2 0) < k_pre)) (PreH4 : ((Znth v center_dist_2 0) <> k_pre)) (PreH5 : ((Znth v center_dist_2 0) <= k_pre)) (PreH6 : (v < nv)) (PreH7 : (ok <> 0)) (PreH8 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH9 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH10 : (GraphPre nv edges )) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH14 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH15 : (ec = ((2 * nv ) - 2 ))) (PreH16 : (0 <= v)) (PreH17 : (v <= nv)) (PreH18 : (SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center center_parent_2 center_dist_2 degree_data_2 v ok )) ,
  (IntArray.full deg_p_2 nv degree_data_2 )
  **  (IntArray.full d nv center_dist_2 )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full p nv center_parent_2 )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (center_parent: (@list Z))  (center_dist: (@list Z))  (degree_data: (@list Z))  (head_data: (@list Z))  (to_data: (@list Z))  (next_data: (@list Z))  (second_parent: (@list Z))  (second_dist: (@list Z))  (first_parent: (@list Z))  (first_dist: (@list Z)) ,
  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data (v + 1 ) 0 ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
) \/
(
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (center: Z) (center_parent_2: (@list Z)) (center_dist_2: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : ((Znth v degree_data_2 0) < 3)) (PreH2 : (v = center)) (PreH3 : ((Znth v center_dist_2 0) < k_pre)) (PreH4 : ((Znth v center_dist_2 0) <> k_pre)) (PreH5 : ((Znth v center_dist_2 0) <= k_pre)) (PreH6 : (v < nv)) (PreH7 : (ok <> 0)) (PreH8 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH9 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH10 : (GraphPre nv edges )) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH14 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH15 : (ec = ((2 * nv ) - 2 ))) (PreH16 : (0 <= v)) (PreH17 : (v <= nv)) (PreH18 : (SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center center_parent_2 center_dist_2 degree_data_2 v ok )) ,
  TT && emp 
|--
  EX (second_parent: (@list Z))  (second_dist: (@list Z)) ,
  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (0 <= (center + 1 )) ” 
  &&  “ ((center + 1 ) <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent_2 center_dist_2 degree_data_2 (center + 1 ) 0 ) ”
  &&  emp
).

Definition solver_entail_wit_14_4 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (center: Z) (center_parent_2: (@list Z)) (center_dist_2: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : ((Znth v degree_data_2 0) < 4)) (PreH2 : (v <> center)) (PreH3 : (v <> center)) (PreH4 : ((Znth v center_dist_2 0) < k_pre)) (PreH5 : ((Znth v center_dist_2 0) <> k_pre)) (PreH6 : ((Znth v center_dist_2 0) <= k_pre)) (PreH7 : (v < nv)) (PreH8 : (ok <> 0)) (PreH9 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH10 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH11 : (GraphPre nv edges )) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH15 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH16 : (ec = ((2 * nv ) - 2 ))) (PreH17 : (0 <= v)) (PreH18 : (v <= nv)) (PreH19 : (SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center center_parent_2 center_dist_2 degree_data_2 v ok )) ,
  (IntArray.full deg_p_2 nv degree_data_2 )
  **  (IntArray.full d nv center_dist_2 )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full p nv center_parent_2 )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (center_parent: (@list Z))  (center_dist: (@list Z))  (degree_data: (@list Z))  (head_data: (@list Z))  (to_data: (@list Z))  (next_data: (@list Z))  (second_parent: (@list Z))  (second_dist: (@list Z))  (first_parent: (@list Z))  (first_dist: (@list Z)) ,
  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data (v + 1 ) 0 ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
) \/
(
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (center: Z) (center_parent_2: (@list Z)) (center_dist_2: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : ((Znth v degree_data_2 0) < 4)) (PreH2 : (v <> center)) (PreH3 : (v <> center)) (PreH4 : ((Znth v center_dist_2 0) < k_pre)) (PreH5 : ((Znth v center_dist_2 0) <> k_pre)) (PreH6 : ((Znth v center_dist_2 0) <= k_pre)) (PreH7 : (v < nv)) (PreH8 : (ok <> 0)) (PreH9 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH10 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH11 : (GraphPre nv edges )) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH15 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH16 : (ec = ((2 * nv ) - 2 ))) (PreH17 : (0 <= v)) (PreH18 : (v <= nv)) (PreH19 : (SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center center_parent_2 center_dist_2 degree_data_2 v ok )) ,
  TT && emp 
|--
  EX (second_parent: (@list Z))  (second_dist: (@list Z)) ,
  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (0 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent_2 center_dist_2 degree_data_2 (v + 1 ) 0 ) ”
  &&  emp
).

Definition solver_entail_wit_14_5 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (center: Z) (center_parent_2: (@list Z)) (center_dist_2: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : ((Znth v degree_data_2 0) >= 4)) (PreH2 : (v <> center)) (PreH3 : (v <> center)) (PreH4 : ((Znth v center_dist_2 0) < k_pre)) (PreH5 : ((Znth v center_dist_2 0) <> k_pre)) (PreH6 : ((Znth v center_dist_2 0) <= k_pre)) (PreH7 : (v < nv)) (PreH8 : (ok <> 0)) (PreH9 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH10 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH11 : (GraphPre nv edges )) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH15 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH16 : (ec = ((2 * nv ) - 2 ))) (PreH17 : (0 <= v)) (PreH18 : (v <= nv)) (PreH19 : (SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center center_parent_2 center_dist_2 degree_data_2 v ok )) ,
  (IntArray.full deg_p_2 nv degree_data_2 )
  **  (IntArray.full d nv center_dist_2 )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full p nv center_parent_2 )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (center_parent: (@list Z))  (center_dist: (@list Z))  (degree_data: (@list Z))  (head_data: (@list Z))  (to_data: (@list Z))  (next_data: (@list Z))  (second_parent: (@list Z))  (second_dist: (@list Z))  (first_parent: (@list Z))  (first_dist: (@list Z)) ,
  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data (v + 1 ) ok ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
) \/
(
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (center: Z) (center_parent_2: (@list Z)) (center_dist_2: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : ((Znth v degree_data_2 0) >= 4)) (PreH2 : (v <> center)) (PreH3 : (v <> center)) (PreH4 : ((Znth v center_dist_2 0) < k_pre)) (PreH5 : ((Znth v center_dist_2 0) <> k_pre)) (PreH6 : ((Znth v center_dist_2 0) <= k_pre)) (PreH7 : (v < nv)) (PreH8 : (ok <> 0)) (PreH9 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH10 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH11 : (GraphPre nv edges )) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH15 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH16 : (ec = ((2 * nv ) - 2 ))) (PreH17 : (0 <= v)) (PreH18 : (v <= nv)) (PreH19 : (SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center center_parent_2 center_dist_2 degree_data_2 v ok )) ,
  TT && emp 
|--
  EX (second_parent: (@list Z))  (second_dist: (@list Z)) ,
  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (0 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent_2 center_dist_2 degree_data_2 (v + 1 ) ok ) ”
  &&  emp
).

Definition solver_entail_wit_14_6 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (center: Z) (center_parent_2: (@list Z)) (center_dist_2: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : (v = center)) (PreH2 : ((Znth v degree_data_2 0) >= 3)) (PreH3 : (v = center)) (PreH4 : ((Znth v center_dist_2 0) < k_pre)) (PreH5 : ((Znth v center_dist_2 0) <> k_pre)) (PreH6 : ((Znth v center_dist_2 0) <= k_pre)) (PreH7 : (v < nv)) (PreH8 : (ok <> 0)) (PreH9 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH10 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH11 : (GraphPre nv edges )) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH15 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH16 : (ec = ((2 * nv ) - 2 ))) (PreH17 : (0 <= v)) (PreH18 : (v <= nv)) (PreH19 : (SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center center_parent_2 center_dist_2 degree_data_2 v ok )) ,
  (IntArray.full deg_p_2 nv degree_data_2 )
  **  (IntArray.full d nv center_dist_2 )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full p nv center_parent_2 )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (center_parent: (@list Z))  (center_dist: (@list Z))  (degree_data: (@list Z))  (head_data: (@list Z))  (to_data: (@list Z))  (next_data: (@list Z))  (second_parent: (@list Z))  (second_dist: (@list Z))  (first_parent: (@list Z))  (first_dist: (@list Z)) ,
  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data (v + 1 ) ok ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
) \/
(
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (center: Z) (center_parent_2: (@list Z)) (center_dist_2: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : (v = center)) (PreH2 : ((Znth v degree_data_2 0) >= 3)) (PreH3 : (v = center)) (PreH4 : ((Znth v center_dist_2 0) < k_pre)) (PreH5 : ((Znth v center_dist_2 0) <> k_pre)) (PreH6 : ((Znth v center_dist_2 0) <= k_pre)) (PreH7 : (v < nv)) (PreH8 : (ok <> 0)) (PreH9 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH10 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH11 : (GraphPre nv edges )) (PreH12 : (1 <= k_pre)) (PreH13 : (k_pre <= 1000000000)) (PreH14 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH15 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH16 : (ec = ((2 * nv ) - 2 ))) (PreH17 : (0 <= v)) (PreH18 : (v <= nv)) (PreH19 : (SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center center_parent_2 center_dist_2 degree_data_2 v ok )) ,
  TT && emp 
|--
  EX (second_parent: (@list Z))  (second_dist: (@list Z)) ,
  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (0 <= (center + 1 )) ” 
  &&  “ ((center + 1 ) <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent_2 center_dist_2 degree_data_2 (center + 1 ) ok ) ”
  &&  emp
).

Definition solver_entail_wit_14_7 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (center: Z) (center_parent_2: (@list Z)) (center_dist_2: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : ((Znth v center_dist_2 0) >= k_pre)) (PreH2 : ((Znth v degree_data_2 0) = 1)) (PreH3 : ((Znth v center_dist_2 0) = k_pre)) (PreH4 : ((Znth v center_dist_2 0) <= k_pre)) (PreH5 : (v < nv)) (PreH6 : (ok <> 0)) (PreH7 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH8 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH9 : (GraphPre nv edges )) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 1000000000)) (PreH12 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH13 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH14 : (ec = ((2 * nv ) - 2 ))) (PreH15 : (0 <= v)) (PreH16 : (v <= nv)) (PreH17 : (SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center center_parent_2 center_dist_2 degree_data_2 v ok )) ,
  (IntArray.full d nv center_dist_2 )
  **  (IntArray.full deg_p_2 nv degree_data_2 )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full p nv center_parent_2 )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (center_parent: (@list Z))  (center_dist: (@list Z))  (degree_data: (@list Z))  (head_data: (@list Z))  (to_data: (@list Z))  (next_data: (@list Z))  (second_parent: (@list Z))  (second_dist: (@list Z))  (first_parent: (@list Z))  (first_dist: (@list Z)) ,
  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data (v + 1 ) ok ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
) \/
(
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (center: Z) (center_parent_2: (@list Z)) (center_dist_2: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : ((Znth v center_dist_2 0) >= k_pre)) (PreH2 : ((Znth v degree_data_2 0) = 1)) (PreH3 : ((Znth v center_dist_2 0) = k_pre)) (PreH4 : ((Znth v center_dist_2 0) <= k_pre)) (PreH5 : (v < nv)) (PreH6 : (ok <> 0)) (PreH7 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH8 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH9 : (GraphPre nv edges )) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 1000000000)) (PreH12 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH13 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH14 : (ec = ((2 * nv ) - 2 ))) (PreH15 : (0 <= v)) (PreH16 : (v <= nv)) (PreH17 : (SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center center_parent_2 center_dist_2 degree_data_2 v ok )) ,
  TT && emp 
|--
  EX (second_parent: (@list Z))  (second_dist: (@list Z)) ,
  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (0 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= nv) ” 
  &&  “ (SolverDecision nv (Znth v center_dist_2 0) edges second_parent second_dist b center center_parent_2 center_dist_2 degree_data_2 (v + 1 ) ok ) ”
  &&  emp
).

Definition solver_entail_wit_15_1 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (center: Z) (center_parent_2: (@list Z)) (center_dist_2: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : (ok = 0)) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH4 : (GraphPre nv edges )) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH8 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH9 : (ec = ((2 * nv ) - 2 ))) (PreH10 : (0 <= v)) (PreH11 : (v <= nv)) (PreH12 : (SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center center_parent_2 center_dist_2 degree_data_2 v ok )) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full deg_p_2 nv degree_data_2 )
  **  (IntArray.full p nv center_parent_2 )
  **  (IntArray.full d nv center_dist_2 )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (head_data: (@list Z))  (to_data: (@list Z))  (next_data: (@list Z))  (first_parent: (@list Z))  (first_dist: (@list Z))  (second_parent: (@list Z))  (second_dist: (@list Z))  (center_parent: (@list Z))  (center_dist: (@list Z))  (degree_data: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok ) ” 
  &&  “ (Spec nv k_pre edges ok ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
) \/
(
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (center: Z) (center_parent_2: (@list Z)) (center_dist_2: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : (ok = 0)) (PreH2 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH3 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH4 : (GraphPre nv edges )) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH8 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH9 : (ec = ((2 * nv ) - 2 ))) (PreH10 : (0 <= v)) (PreH11 : (v <= nv)) (PreH12 : (SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center center_parent_2 center_dist_2 degree_data_2 v ok )) ,
  TT && emp 
|--
  EX (first_parent: (@list Z))  (first_dist: (@list Z))  (second_parent: (@list Z))  (second_dist: (@list Z)) ,
  “ (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent_2 center_dist_2 degree_data_2 0 ) ” 
  &&  “ (Spec nv k_pre edges 0 ) ”
  &&  emp
).

Definition solver_entail_wit_15_2 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p_2: Z) (next_p_2: Z) (to_p_2: Z) (head_p_2: Z) (center: Z) (center_parent_2: (@list Z)) (center_dist_2: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : (v >= nv)) (PreH2 : (ok <> 0)) (PreH3 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH4 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH5 : (GraphPre nv edges )) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH9 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH10 : (ec = ((2 * nv ) - 2 ))) (PreH11 : (0 <= v)) (PreH12 : (v <= nv)) (PreH13 : (SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center center_parent_2 center_dist_2 degree_data_2 v ok )) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p_2)
  **  ((( &( "to" ) )) # Ptr  |-> to_p_2)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p_2)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p_2)
  **  (IntArray.full head_p_2 nv head_data_2 )
  **  (IntArray.full to_p_2 ((2 * nv ) - 2 ) to_data_2 )
  **  (IntArray.full next_p_2 ((2 * nv ) - 2 ) next_data_2 )
  **  (IntArray.full deg_p_2 nv degree_data_2 )
  **  (IntArray.full p nv center_parent_2 )
  **  (IntArray.full d nv center_dist_2 )
|--
  EX (deg_p: Z)  (next_p: Z)  (to_p: Z)  (head_p: Z)  (head_data: (@list Z))  (to_data: (@list Z))  (next_data: (@list Z))  (first_parent: (@list Z))  (first_dist: (@list Z))  (second_parent: (@list Z))  (second_dist: (@list Z))  (center_parent: (@list Z))  (center_dist: (@list Z))  (degree_data: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok ) ” 
  &&  “ (Spec nv k_pre edges ok ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
) \/
(
forall (k_pre: Z) (edges: (@list (Z * Z))) (nv: Z) (center: Z) (center_parent_2: (@list Z)) (center_dist_2: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data_2: (@list Z)) (head_data_2: (@list Z)) (to_data_2: (@list Z)) (next_data_2: (@list Z)) (second_parent_2: (@list Z)) (second_dist_2: (@list Z)) (b: Z) (first_parent_2: (@list Z)) (first_dist_2: (@list Z)) (a: Z) (PreH1 : (v >= nv)) (PreH2 : (ok <> 0)) (PreH3 : (BFSResult nv edges 0 first_parent_2 first_dist_2 a )) (PreH4 : (BFSResult nv edges a second_parent_2 second_dist_2 b )) (PreH5 : (GraphPre nv edges )) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : (AdjacencyModel nv edges head_data_2 to_data_2 next_data_2 )) (PreH9 : (DegreePrefix nv edges (nv - 1 ) degree_data_2 )) (PreH10 : (ec = ((2 * nv ) - 2 ))) (PreH11 : (0 <= v)) (PreH12 : (v <= nv)) (PreH13 : (SolverDecision nv k_pre edges second_parent_2 second_dist_2 b center center_parent_2 center_dist_2 degree_data_2 v ok )) ,
  TT && emp 
|--
  EX (first_parent: (@list Z))  (first_dist: (@list Z))  (second_parent: (@list Z))  (second_dist: (@list Z)) ,
  “ (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent_2 center_dist_2 degree_data_2 ok ) ” 
  &&  “ (Spec nv k_pre edges ok ) ”
  &&  emp
).

Definition solver_return_wit_1 := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (GraphPre nv edges )) (PreH5 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH6 : (Spec nv k_pre edges ok )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
|--
  EX (deg_after: Z)  (next_after: Z)  (to_after: Z)  (head_after: Z) ,
  “ (Spec nv k_pre edges ok ) ”
  &&  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_after)
  **  ((( &( "to" ) )) # Ptr  |-> to_after)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_after)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_after)
) \/
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (GraphPre nv edges )) (PreH5 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH6 : (Spec nv k_pre edges ok )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
|--
  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
).

Definition solver_return_wit_1_split_goal_spatial := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (GraphPre nv edges )) (PreH5 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH6 : (Spec nv k_pre edges ok )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
|--
  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
.

Definition solver_partial_solve_wit_1_pure := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (deg_before: Z) (next_before: Z) (to_before: Z) (head_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z)  __default__Prod_Z_Z (PreH1 : (1 <= nv)) (PreH2 : (nv <= 100000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (edges)) = (nv - 1 ))) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH7 : (Pre nv k_pre edges )) (PreH8 : (nn_pre = nv)) (PreH9 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH10 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_before)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_before)
|--
  “ (0 <= nv) ” 
  &&  “ ((nn_pre * sizeof(INT) ) = (nv * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (deg_before: Z) (next_before: Z) (to_before: Z) (head_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z)  __default__Prod_Z_Z (PreH1 : (1 <= nv)) (PreH2 : (nv <= 100000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (edges)) = (nv - 1 ))) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH7 : (Pre nv k_pre edges )) (PreH8 : (nn_pre = nv)) (PreH9 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH10 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_before)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_before)
|--
  “ (0 <= nv) ” 
  &&  “ ((nn_pre * sizeof(INT) ) = (nv * sizeof(INT) )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (edges)) = (nv - 1 )) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (nn_pre = nv) ” 
  &&  “ ((Zlength (eu_data)) = (Zlength (edges))) ” 
  &&  “ ((Zlength (ev_data)) = (Zlength (edges))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_before)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_before)
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (deg_before: Z) (next_before: Z) (to_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : ((Zlength (edges)) = (nv - 1 ))) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH8 : (Pre nv k_pre edges )) (PreH9 : (nn_pre = nv)) (PreH10 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH11 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_before)
|--
  “ (0 <= nv) ” 
  &&  “ (nn_pre = nv) ” 
  &&  “ (sizeof(INT) = sizeof(INT)) ”
.

Definition solver_partial_solve_wit_2_aux := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (deg_before: Z) (next_before: Z) (to_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : ((Zlength (edges)) = (nv - 1 ))) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH8 : (Pre nv k_pre edges )) (PreH9 : (nn_pre = nv)) (PreH10 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH11 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.undef_full retval nv )
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_before)
|--
  “ (0 <= nv) ” 
  &&  “ (nn_pre = nv) ” 
  &&  “ (sizeof(INT) = sizeof(INT)) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (edges)) = (nv - 1 )) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (nn_pre = nv) ” 
  &&  “ ((Zlength (eu_data)) = (Zlength (edges))) ” 
  &&  “ ((Zlength (ev_data)) = (Zlength (edges))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (IntArray.undef_full retval nv )
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_before)
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3_pure := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (next_before: Z) (to_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= nv)) (PreH4 : (nv <= 100000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (edges)) = (nv - 1 ))) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH9 : (Pre nv k_pre edges )) (PreH10 : (nn_pre = nv)) (PreH11 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH12 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full retval_2 nv (repeat_Z (0) (nv)) )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> retval_2)
|--
  “ (0 <= ((2 * nv ) - 2 )) ” 
  &&  “ ((((2 * nn_pre ) - 2 ) * sizeof(INT) ) = (((2 * nv ) - 2 ) * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_3_aux := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (next_before: Z) (to_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= nv)) (PreH4 : (nv <= 100000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (edges)) = (nv - 1 ))) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH9 : (Pre nv k_pre edges )) (PreH10 : (nn_pre = nv)) (PreH11 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH12 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full retval_2 nv (repeat_Z (0) (nv)) )
  **  (IntArray.undef_full retval nv )
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> retval_2)
|--
  “ (0 <= ((2 * nv ) - 2 )) ” 
  &&  “ ((((2 * nn_pre ) - 2 ) * sizeof(INT) ) = (((2 * nv ) - 2 ) * sizeof(INT) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (edges)) = (nv - 1 )) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (nn_pre = nv) ” 
  &&  “ ((Zlength (eu_data)) = (Zlength (edges))) ” 
  &&  “ ((Zlength (ev_data)) = (Zlength (edges))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (IntArray.full retval_2 nv (repeat_Z (0) (nv)) )
  **  (IntArray.undef_full retval nv )
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> to_before)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> retval_2)
.

Definition solver_partial_solve_wit_3 := solver_partial_solve_wit_3_pure -> solver_partial_solve_wit_3_aux.

Definition solver_partial_solve_wit_4_pure := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (next_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod_Z_Z (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= nv)) (PreH5 : (nv <= 100000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : ((Zlength (edges)) = (nv - 1 ))) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH10 : (Pre nv k_pre edges )) (PreH11 : (nn_pre = nv)) (PreH12 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH13 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH14 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.undef_full retval_3 ((2 * nv ) - 2 ) )
  **  (IntArray.full retval_2 nv (repeat_Z (0) (nv)) )
  **  (IntArray.undef_full retval nv )
  **  ((( &( "nn" ) )) # Int  |-> nn_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> retval_3)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> retval_2)
|--
  “ (0 <= ((2 * nv ) - 2 )) ” 
  &&  “ ((((2 * nn_pre ) - 2 ) * sizeof(INT) ) = (((2 * nv ) - 2 ) * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_4_aux := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (nn_pre: Z) (next_before: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod_Z_Z (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= nv)) (PreH5 : (nv <= 100000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : ((Zlength (edges)) = (nv - 1 ))) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv)))) (PreH10 : (Pre nv k_pre edges )) (PreH11 : (nn_pre = nv)) (PreH12 : ((Zlength (eu_data)) = (Zlength (edges)))) (PreH13 : ((Zlength (ev_data)) = (Zlength (edges)))) (PreH14 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.undef_full retval_3 ((2 * nv ) - 2 ) )
  **  (IntArray.full retval_2 nv (repeat_Z (0) (nv)) )
  **  (IntArray.undef_full retval nv )
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> retval_3)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> retval_2)
|--
  “ (0 <= ((2 * nv ) - 2 )) ” 
  &&  “ ((((2 * nn_pre ) - 2 ) * sizeof(INT) ) = (((2 * nv ) - 2 ) * sizeof(INT) )) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (edges)) = (nv - 1 )) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> ((((1 <= (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i edges __default__Prod_Z_Z))) <= nv)) /\ (1 <= (snd ((Znth i edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i edges __default__Prod_Z_Z))) <= nv))) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (nn_pre = nv) ” 
  &&  “ ((Zlength (eu_data)) = (Zlength (edges))) ” 
  &&  “ ((Zlength (ev_data)) = (Zlength (edges))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (edges)))) -> (((Znth i_2 eu_data 0) = ((fst ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )) /\ ((Znth i_2 ev_data 0) = ((snd ((Znth i_2 edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (IntArray.undef_full retval_3 ((2 * nv ) - 2 ) )
  **  (IntArray.full retval_2 nv (repeat_Z (0) (nv)) )
  **  (IntArray.undef_full retval nv )
  **  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nn_pre)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "to" ) )) # Ptr  |-> retval_3)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_before)
  **  ((( &( "deg" ) )) # Ptr  |-> retval_2)
.

Definition solver_partial_solve_wit_4 := solver_partial_solve_wit_4_pure -> solver_partial_solve_wit_4_aux.

Definition solver_partial_solve_wit_5 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (head_init: (@list Z)) (i: Z)  __default__Prod_Z_Z (PreH1 : (i < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (GraphPre nv edges )) (PreH8 : (0 <= i)) (PreH9 : (i <= nv)) (PreH10 : ((Zlength (head_init)) = i)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1)))) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.seg head_p 0 i head_init )
  **  (IntArray.undef_seg head_p i nv )
  **  (IntArray.undef_full to_p ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv (repeat_Z (0) (nv)) )
|--
  “ (i < nv) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nv) ” 
  &&  “ ((Zlength (head_init)) = i) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < i)) -> ((Znth q head_init 0) = (-1))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((head_p + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg head_p (i + 1 ) nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.seg head_p 0 i head_init )
  **  (IntArray.undef_full to_p ((2 * nv ) - 2 ) )
  **  (IntArray.undef_full next_p ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv (repeat_Z (0) (nv)) )
.

Definition solver_partial_solve_wit_6 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 ec to_done )
  **  (IntArray.undef_seg to_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv degree_data )
|--
  “ ((i + 1 ) < nv) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (nv - 1 )) ” 
  &&  “ (ec = (2 * i )) ” 
  &&  “ ((Zlength (head_data)) = nv) ” 
  &&  “ ((Zlength (to_done)) = ec) ” 
  &&  “ ((Zlength (next_done)) = ec) ” 
  &&  “ ((Zlength (degree_data)) = nv) ” 
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ” 
  &&  “ (DegreePrefix nv edges i degree_data ) ” 
  &&  “ forall (index: Z) , (CurrentEdgeFresh edges index ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((ev_pre + (i * sizeof(INT)))) # Int  |-> (Znth i ev_data 0))
  **  (IntArray.missing_i ev_pre i 0 (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 ec to_done )
  **  (IntArray.undef_seg to_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv degree_data )
.

Definition solver_partial_solve_wit_7 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 ec to_done )
  **  (IntArray.undef_seg to_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv degree_data )
|--
  “ ((i + 1 ) < nv) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (nv - 1 )) ” 
  &&  “ (ec = (2 * i )) ” 
  &&  “ ((Zlength (head_data)) = nv) ” 
  &&  “ ((Zlength (to_done)) = ec) ” 
  &&  “ ((Zlength (next_done)) = ec) ” 
  &&  “ ((Zlength (degree_data)) = nv) ” 
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ” 
  &&  “ (DegreePrefix nv edges i degree_data ) ” 
  &&  “ forall (index: Z) , (CurrentEdgeFresh edges index ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((eu_pre + (i * sizeof(INT)))) # Int  |-> (Znth i eu_data 0))
  **  (IntArray.missing_i eu_pre i 0 (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 ec to_done )
  **  (IntArray.undef_seg to_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv degree_data )
.

Definition solver_partial_solve_wit_8 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 ec to_done )
  **  (IntArray.undef_seg to_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv degree_data )
|--
  “ ((i + 1 ) < nv) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (nv - 1 )) ” 
  &&  “ (ec = (2 * i )) ” 
  &&  “ ((Zlength (head_data)) = nv) ” 
  &&  “ ((Zlength (to_done)) = ec) ” 
  &&  “ ((Zlength (next_done)) = ec) ” 
  &&  “ ((Zlength (degree_data)) = nv) ” 
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ” 
  &&  “ (DegreePrefix nv edges i degree_data ) ” 
  &&  “ forall (index: Z) , (CurrentEdgeFresh edges index ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((to_p + (ec * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg to_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 ec to_done )
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv degree_data )
.

Definition solver_partial_solve_wit_9 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.seg to_p 0 (ec + 1 ) (app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv degree_data )
|--
  “ ((i + 1 ) < nv) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (nv - 1 )) ” 
  &&  “ (ec = (2 * i )) ” 
  &&  “ ((Zlength (head_data)) = nv) ” 
  &&  “ ((Zlength (to_done)) = ec) ” 
  &&  “ ((Zlength (next_done)) = ec) ” 
  &&  “ ((Zlength (degree_data)) = nv) ” 
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ” 
  &&  “ (DegreePrefix nv edges i degree_data ) ” 
  &&  “ forall (index: Z) , (CurrentEdgeFresh edges index ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((head_p + ((Znth i eu_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i eu_data 0) head_data 0))
  **  (IntArray.missing_i head_p (Znth i eu_data 0) 0 nv head_data )
  **  (IntArray.seg to_p 0 (ec + 1 ) (app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv degree_data )
.

Definition solver_partial_solve_wit_10 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 (ec + 1 ) (app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.undef_seg next_p ec ((2 * nv ) - 2 ) )
  **  (IntArray.full deg_p nv degree_data )
|--
  “ ((i + 1 ) < nv) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (nv - 1 )) ” 
  &&  “ (ec = (2 * i )) ” 
  &&  “ ((Zlength (head_data)) = nv) ” 
  &&  “ ((Zlength (to_done)) = ec) ” 
  &&  “ ((Zlength (next_done)) = ec) ” 
  &&  “ ((Zlength (degree_data)) = nv) ” 
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ” 
  &&  “ (DegreePrefix nv edges i degree_data ) ” 
  &&  “ forall (index: Z) , (CurrentEdgeFresh edges index ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((next_p + (ec * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg next_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 (ec + 1 ) (app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.seg next_p 0 ec next_done )
  **  (IntArray.full deg_p nv degree_data )
.

Definition solver_partial_solve_wit_11 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.seg next_p 0 (ec + 1 ) (app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.seg to_p 0 (ec + 1 ) (app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
|--
  “ ((i + 1 ) < nv) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (nv - 1 )) ” 
  &&  “ (ec = (2 * i )) ” 
  &&  “ ((Zlength (head_data)) = nv) ” 
  &&  “ ((Zlength (to_done)) = ec) ” 
  &&  “ ((Zlength (next_done)) = ec) ” 
  &&  “ ((Zlength (degree_data)) = nv) ” 
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ” 
  &&  “ (DegreePrefix nv edges i degree_data ) ” 
  &&  “ forall (index: Z) , (CurrentEdgeFresh edges index ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((head_p + ((Znth i eu_data 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i head_p (Znth i eu_data 0) 0 nv head_data )
  **  (IntArray.seg next_p 0 (ec + 1 ) (app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 (ec + 1 ) (app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
.

Definition solver_partial_solve_wit_12 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full head_p nv (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) )
  **  (IntArray.seg next_p 0 (ec + 1 ) (app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 (ec + 1 ) (app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
|--
  “ ((i + 1 ) < nv) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (nv - 1 )) ” 
  &&  “ (ec = (2 * i )) ” 
  &&  “ ((Zlength (head_data)) = nv) ” 
  &&  “ ((Zlength (to_done)) = ec) ” 
  &&  “ ((Zlength (next_done)) = ec) ” 
  &&  “ ((Zlength (degree_data)) = nv) ” 
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ” 
  &&  “ (DegreePrefix nv edges i degree_data ) ” 
  &&  “ forall (index: Z) , (CurrentEdgeFresh edges index ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((to_p + ((ec + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) )
  **  (IntArray.seg next_p 0 (ec + 1 ) (app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 (ec + 1 ) (app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z))))) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
.

Definition solver_partial_solve_wit_13 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) )
  **  (IntArray.seg next_p 0 (ec + 1 ) (app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
|--
  “ ((i + 1 ) < nv) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (nv - 1 )) ” 
  &&  “ (ec = (2 * i )) ” 
  &&  “ ((Zlength (head_data)) = nv) ” 
  &&  “ ((Zlength (to_done)) = ec) ” 
  &&  “ ((Zlength (next_done)) = ec) ” 
  &&  “ ((Zlength (degree_data)) = nv) ” 
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ” 
  &&  “ (DegreePrefix nv edges i degree_data ) ” 
  &&  “ forall (index: Z) , (CurrentEdgeFresh edges index ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((head_p + ((Znth i ev_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0))
  **  (IntArray.missing_i head_p (Znth i ev_data 0) 0 nv (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 (ec + 1 ) (app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
.

Definition solver_partial_solve_wit_14 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full head_p nv (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 (ec + 1 ) (app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p (ec + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
|--
  “ ((i + 1 ) < nv) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (nv - 1 )) ” 
  &&  “ (ec = (2 * i )) ” 
  &&  “ ((Zlength (head_data)) = nv) ” 
  &&  “ ((Zlength (to_done)) = ec) ” 
  &&  “ ((Zlength (next_done)) = ec) ” 
  &&  “ ((Zlength (degree_data)) = nv) ” 
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ” 
  &&  “ (DegreePrefix nv edges i degree_data ) ” 
  &&  “ forall (index: Z) , (CurrentEdgeFresh edges index ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((next_p + ((ec + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg next_p 0 (ec + 1 ) (app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z))))) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
.

Definition solver_partial_solve_wit_15 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
|--
  “ ((i + 1 ) < nv) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (nv - 1 )) ” 
  &&  “ (ec = (2 * i )) ” 
  &&  “ ((Zlength (head_data)) = nv) ” 
  &&  “ ((Zlength (to_done)) = ec) ” 
  &&  “ ((Zlength (next_done)) = ec) ” 
  &&  “ ((Zlength (degree_data)) = nv) ” 
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ” 
  &&  “ (DegreePrefix nv edges i degree_data ) ” 
  &&  “ forall (index: Z) , (CurrentEdgeFresh edges index ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((head_p + ((Znth i ev_data 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i head_p (Znth i ev_data 0) 0 nv (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
.

Definition solver_partial_solve_wit_16 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
|--
  “ ((i + 1 ) < nv) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (nv - 1 )) ” 
  &&  “ (ec = (2 * i )) ” 
  &&  “ ((Zlength (head_data)) = nv) ” 
  &&  “ ((Zlength (to_done)) = ec) ” 
  &&  “ ((Zlength (next_done)) = ec) ” 
  &&  “ ((Zlength (degree_data)) = nv) ” 
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ” 
  &&  “ (DegreePrefix nv edges i degree_data ) ” 
  &&  “ forall (index: Z) , (CurrentEdgeFresh edges index ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((deg_p + ((Znth i eu_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i eu_data 0) degree_data 0))
  **  (IntArray.missing_i deg_p (Znth i eu_data 0) 0 nv degree_data )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
.

Definition solver_partial_solve_wit_17 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
|--
  “ ((i + 1 ) < nv) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (nv - 1 )) ” 
  &&  “ (ec = (2 * i )) ” 
  &&  “ ((Zlength (head_data)) = nv) ” 
  &&  “ ((Zlength (to_done)) = ec) ” 
  &&  “ ((Zlength (next_done)) = ec) ” 
  &&  “ ((Zlength (degree_data)) = nv) ” 
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ” 
  &&  “ (DegreePrefix nv edges i degree_data ) ” 
  &&  “ forall (index: Z) , (CurrentEdgeFresh edges index ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((deg_p + ((Znth i eu_data 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i deg_p (Znth i eu_data 0) 0 nv degree_data )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
.

Definition solver_partial_solve_wit_18 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full deg_p nv (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data 0) + 1 )) (degree_data)) )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
|--
  “ ((i + 1 ) < nv) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (nv - 1 )) ” 
  &&  “ (ec = (2 * i )) ” 
  &&  “ ((Zlength (head_data)) = nv) ” 
  &&  “ ((Zlength (to_done)) = ec) ” 
  &&  “ ((Zlength (next_done)) = ec) ” 
  &&  “ ((Zlength (degree_data)) = nv) ” 
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ” 
  &&  “ (DegreePrefix nv edges i degree_data ) ” 
  &&  “ forall (index: Z) , (CurrentEdgeFresh edges index ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((deg_p + ((Znth i ev_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data 0) + 1 )) (degree_data)) 0))
  **  (IntArray.missing_i deg_p (Znth i ev_data 0) 0 nv (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data 0) + 1 )) (degree_data)) )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
.

Definition solver_partial_solve_wit_19 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (degree_data: (@list Z)) (next_done: (@list Z)) (to_done: (@list Z)) (head_data: (@list Z)) (ec: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : ((i + 1 ) < nv)) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (0 <= i)) (PreH8 : (i <= (nv - 1 ))) (PreH9 : (ec = (2 * i ))) (PreH10 : ((Zlength (head_data)) = nv)) (PreH11 : ((Zlength (to_done)) = ec)) (PreH12 : ((Zlength (next_done)) = ec)) (PreH13 : ((Zlength (degree_data)) = nv)) (PreH14 : (AdjacencyBuildState nv edges i head_data to_done next_done )) (PreH15 : (DegreePrefix nv edges i degree_data )) (PreH16 : forall (index: Z) , (CurrentEdgeFresh edges index )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 ))))) ,
  (IntArray.full deg_p nv (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data 0) + 1 )) (degree_data)) )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
|--
  “ ((i + 1 ) < nv) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (nv - 1 )) ” 
  &&  “ (ec = (2 * i )) ” 
  &&  “ ((Zlength (head_data)) = nv) ” 
  &&  “ ((Zlength (to_done)) = ec) ” 
  &&  “ ((Zlength (next_done)) = ec) ” 
  &&  “ ((Zlength (degree_data)) = nv) ” 
  &&  “ (AdjacencyBuildState nv edges i head_data to_done next_done ) ” 
  &&  “ (DegreePrefix nv edges i degree_data ) ” 
  &&  “ forall (index: Z) , (CurrentEdgeFresh edges index ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (nv - 1 ))) -> ((((((0 <= (Znth j eu_data 0)) /\ ((Znth j eu_data 0) < nv)) /\ (0 <= (Znth j ev_data 0))) /\ ((Znth j ev_data 0) < nv)) /\ ((Znth j eu_data 0) = ((fst ((Znth j edges __default__Prod_Z_Z))) - 1 ))) /\ ((Znth j ev_data 0) = ((snd ((Znth j edges __default__Prod_Z_Z))) - 1 )))) ”
  &&  (((deg_p + ((Znth i ev_data 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i deg_p (Znth i ev_data 0) 0 nv (replace_Znth ((Znth i eu_data 0)) (((Znth (Znth i eu_data 0) degree_data 0) + 1 )) (degree_data)) )
  **  (IntArray.full head_p nv (replace_Znth ((Znth i ev_data 0)) ((ec + 1 )) ((replace_Znth ((Znth i eu_data 0)) (ec) (head_data)))) )
  **  (IntArray.seg next_p 0 ((ec + 1 ) + 1 ) (app ((app (next_done) ((cons ((Znth (Znth i eu_data 0) head_data 0)) ((@nil Z)))))) ((cons ((Znth (Znth i ev_data 0) (replace_Znth ((Znth i eu_data 0)) (ec) (head_data)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg next_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.seg to_p 0 ((ec + 1 ) + 1 ) (app ((app (to_done) ((cons ((Znth i ev_data 0)) ((@nil Z)))))) ((cons ((Znth i eu_data 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg to_p ((ec + 1 ) + 1 ) ((2 * nv ) - 2 ) )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
.

Definition solver_partial_solve_wit_20_pure := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (GraphPre nv edges )) (PreH8 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH9 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
|--
  “ (0 <= nv) ” 
  &&  “ ((nv * sizeof(INT) ) = (nv * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_20_aux := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (PreH1 : (ec = ((2 * nv ) - 2 ))) (PreH2 : (1 <= nv)) (PreH3 : (nv <= 100000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre nv k_pre edges )) (PreH7 : (GraphPre nv edges )) (PreH8 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH9 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
|--
  “ (0 <= nv) ” 
  &&  “ ((nv * sizeof(INT) ) = (nv * sizeof(INT) )) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ”
  &&  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
.

Definition solver_partial_solve_wit_20 := solver_partial_solve_wit_20_pure -> solver_partial_solve_wit_20_aux.

Definition solver_partial_solve_wit_21_pure := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= nv)) (PreH4 : (nv <= 100000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : (Pre nv k_pre edges )) (PreH8 : (GraphPre nv edges )) (PreH9 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH10 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  ((( &( "d" ) )) # Ptr  |->_)
  **  (IntArray.full_shape retval nv )
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
|--
  “ (0 <= nv) ” 
  &&  “ ((nv * sizeof(INT) ) = (nv * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_21_aux := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (ec = ((2 * nv ) - 2 ))) (PreH3 : (1 <= nv)) (PreH4 : (nv <= 100000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : (Pre nv k_pre edges )) (PreH8 : (GraphPre nv edges )) (PreH9 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH10 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  (IntArray.full_shape retval nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
|--
  “ (0 <= nv) ” 
  &&  “ ((nv * sizeof(INT) ) = (nv * sizeof(INT) )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ”
  &&  (IntArray.full_shape retval nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
.

Definition solver_partial_solve_wit_21 := solver_partial_solve_wit_21_pure -> solver_partial_solve_wit_21_aux.

Definition solver_partial_solve_wit_22_pure := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= nv)) (PreH5 : (nv <= 100000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : (Pre nv k_pre edges )) (PreH9 : (GraphPre nv edges )) (PreH10 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH11 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "ok" ) )) # Int  |-> 1)
  **  (IntArray.full_shape retval_2 nv )
  **  ((( &( "d" ) )) # Ptr  |-> retval_2)
  **  (IntArray.full_shape retval nv )
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
|--
  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < nv) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
.

Definition solver_partial_solve_wit_22_aux := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= nv)) (PreH5 : (nv <= 100000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : (Pre nv k_pre edges )) (PreH9 : (GraphPre nv edges )) (PreH10 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH11 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  (IntArray.full_shape retval_2 nv )
  **  (IntArray.full_shape retval nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
|--
  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < nv) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre nv k_pre edges ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full_shape retval nv )
  **  (IntArray.full_shape retval_2 nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
.

Definition solver_partial_solve_wit_22 := solver_partial_solve_wit_22_pure -> solver_partial_solve_wit_22_aux.

Definition solver_partial_solve_wit_23_pure := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (a: Z) (ok: Z) (ec: Z) (p: Z) (d: Z) (PreH1 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH2 : (ok = 1)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= nv)) (PreH5 : (nv <= 100000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : (GraphPre nv edges )) (PreH9 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH10 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full_shape p nv )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full_shape d nv )
|--
  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (a < nv) ” 
  &&  “ (0 <= a) ”
) \/
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (a: Z) (ok: Z) (ec: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (ec <= INT_MAX)) (PreH4 : (ok <= INT_MAX)) (PreH5 : (nv <= INT_MAX)) (PreH6 : (a <= INT_MAX)) (PreH7 : (ec >= INT_MIN)) (PreH8 : (ok >= INT_MIN)) (PreH9 : (nv >= INT_MIN)) (PreH10 : (a >= INT_MIN)) (PreH11 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH12 : (ok = 1)) (PreH13 : (ec = ((2 * nv ) - 2 ))) (PreH14 : (1 <= nv)) (PreH15 : (nv <= 100000)) (PreH16 : (1 <= k_pre)) (PreH17 : (k_pre <= 1000000000)) (PreH18 : (GraphPre nv edges )) (PreH19 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH20 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full_shape p nv )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full_shape d nv )
|--
  “ (0 <= a) ” 
  &&  “ (a < nv) ”
).

Definition solver_partial_solve_wit_23_pure_split_goal_1 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (a: Z) (ok: Z) (ec: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (ec <= INT_MAX)) (PreH4 : (ok <= INT_MAX)) (PreH5 : (nv <= INT_MAX)) (PreH6 : (a <= INT_MAX)) (PreH7 : (ec >= INT_MIN)) (PreH8 : (ok >= INT_MIN)) (PreH9 : (nv >= INT_MIN)) (PreH10 : (a >= INT_MIN)) (PreH11 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH12 : (ok = 1)) (PreH13 : (ec = ((2 * nv ) - 2 ))) (PreH14 : (1 <= nv)) (PreH15 : (nv <= 100000)) (PreH16 : (1 <= k_pre)) (PreH17 : (k_pre <= 1000000000)) (PreH18 : (GraphPre nv edges )) (PreH19 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH20 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full_shape p nv )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full_shape d nv )
|--
  “ (0 <= a) ”
.

Definition solver_partial_solve_wit_23_pure_split_goal_2 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (a: Z) (ok: Z) (ec: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (ec <= INT_MAX)) (PreH4 : (ok <= INT_MAX)) (PreH5 : (nv <= INT_MAX)) (PreH6 : (a <= INT_MAX)) (PreH7 : (ec >= INT_MIN)) (PreH8 : (ok >= INT_MIN)) (PreH9 : (nv >= INT_MIN)) (PreH10 : (a >= INT_MIN)) (PreH11 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH12 : (ok = 1)) (PreH13 : (ec = ((2 * nv ) - 2 ))) (PreH14 : (1 <= nv)) (PreH15 : (nv <= 100000)) (PreH16 : (1 <= k_pre)) (PreH17 : (k_pre <= 1000000000)) (PreH18 : (GraphPre nv edges )) (PreH19 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH20 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full_shape p nv )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full_shape d nv )
|--
  “ (a < nv) ”
.

Definition solver_partial_solve_wit_23_aux := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (a: Z) (ok: Z) (ec: Z) (p: Z) (d: Z) (PreH1 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH2 : (ok = 1)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (1 <= nv)) (PreH5 : (nv <= 100000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : (GraphPre nv edges )) (PreH9 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH10 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full_shape p nv )
  **  (IntArray.full_shape d nv )
|--
  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (a < nv) ” 
  &&  “ (0 <= a) ” 
  &&  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (ok = 1) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full_shape p nv )
  **  (IntArray.full_shape d nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
.

Definition solver_partial_solve_wit_23 := solver_partial_solve_wit_23_pure -> solver_partial_solve_wit_23_aux.

Definition solver_partial_solve_wit_24 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (p: Z) (d: Z) (PreH1 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH2 : (BFSResult nv edges a second_parent second_dist b )) (PreH3 : (0 <= a)) (PreH4 : (a < nv)) (PreH5 : (0 <= b)) (PreH6 : (b < nv)) (PreH7 : (ok = 1)) (PreH8 : (ec = ((2 * nv ) - 2 ))) (PreH9 : (1 <= nv)) (PreH10 : (nv <= 100000)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (GraphPre nv edges )) (PreH14 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH15 : (DegreePrefix nv edges (nv - 1 ) degree_data )) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv second_parent )
  **  (IntArray.full d nv second_dist )
|--
  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (0 <= a) ” 
  &&  “ (a < nv) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b < nv) ” 
  &&  “ (ok = 1) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ”
  &&  (((d + (b * sizeof(INT)))) # Int  |-> (Znth b second_dist 0))
  **  (IntArray.missing_i d b 0 nv second_dist )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv second_parent )
.

Definition solver_partial_solve_wit_25 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (i: Z) (ok: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : (i < k_pre)) (PreH2 : (ok <> 0)) (PreH3 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH4 : (BFSResult nv edges a second_parent second_dist b )) (PreH5 : (GraphPre nv edges )) (PreH6 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH7 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH8 : (ec = ((2 * nv ) - 2 ))) (PreH9 : (1 <= nv)) (PreH10 : (nv <= 100000)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (DiameterDecision k_pre second_dist b ok )) (PreH14 : (0 <= i)) (PreH15 : (i <= k_pre)) (PreH16 : (0 <= center)) (PreH17 : (center < nv)) (PreH18 : (AncestorAfter second_parent b i center )) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv second_parent )
  **  (IntArray.full d nv second_dist )
|--
  “ (i < k_pre) ” 
  &&  “ (ok <> 0) ” 
  &&  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (DiameterDecision k_pre second_dist b ok ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= k_pre) ” 
  &&  “ (0 <= center) ” 
  &&  “ (center < nv) ” 
  &&  “ (AncestorAfter second_parent b i center ) ”
  &&  (((p + (center * sizeof(INT)))) # Int  |-> (Znth center second_parent 0))
  **  (IntArray.missing_i p center 0 nv second_parent )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full d nv second_dist )
.

Definition solver_partial_solve_wit_26_pure := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (center: Z) (p: Z) (d: Z) (PreH1 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH2 : (BFSResult nv edges a second_parent second_dist b )) (PreH3 : (GraphPre nv edges )) (PreH4 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH5 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH6 : (ok = 1)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 100000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 1000000000)) (PreH11 : (ec = ((2 * nv ) - 2 ))) (PreH12 : (0 <= center)) (PreH13 : (center < nv)) (PreH14 : (AncestorAfter second_parent b k_pre center )) (PreH15 : ((Znth b second_dist 0) = (2 * k_pre ))) ,
  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full_shape p nv )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full_shape d nv )
|--
  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (0 <= center) ” 
  &&  “ (center < nv) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
.

Definition solver_partial_solve_wit_26_aux := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (a: Z) (b: Z) (ok: Z) (ec: Z) (center: Z) (p: Z) (d: Z) (PreH1 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH2 : (BFSResult nv edges a second_parent second_dist b )) (PreH3 : (GraphPre nv edges )) (PreH4 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH5 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH6 : (ok = 1)) (PreH7 : (1 <= nv)) (PreH8 : (nv <= 100000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 1000000000)) (PreH11 : (ec = ((2 * nv ) - 2 ))) (PreH12 : (0 <= center)) (PreH13 : (center < nv)) (PreH14 : (AncestorAfter second_parent b k_pre center )) (PreH15 : ((Znth b second_dist 0) = (2 * k_pre ))) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full_shape p nv )
  **  (IntArray.full_shape d nv )
|--
  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (0 <= center) ” 
  &&  “ (center < nv) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ok = 1) ” 
  &&  “ (1 <= nv) ” 
  &&  “ (nv <= 100000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= center) ” 
  &&  “ (center < nv) ” 
  &&  “ (AncestorAfter second_parent b k_pre center ) ” 
  &&  “ ((Znth b second_dist 0) = (2 * k_pre )) ”
  &&  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full_shape p nv )
  **  (IntArray.full_shape d nv )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
.

Definition solver_partial_solve_wit_26 := solver_partial_solve_wit_26_pure -> solver_partial_solve_wit_26_aux.

Definition solver_partial_solve_wit_27 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : (v < nv)) (PreH2 : (ok <> 0)) (PreH3 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH4 : (BFSResult nv edges a second_parent second_dist b )) (PreH5 : (GraphPre nv edges )) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH9 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH10 : (ec = ((2 * nv ) - 2 ))) (PreH11 : (0 <= v)) (PreH12 : (v <= nv)) (PreH13 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
|--
  “ (v < nv) ” 
  &&  “ (ok <> 0) ” 
  &&  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok ) ”
  &&  (((d + (v * sizeof(INT)))) # Int  |-> (Znth v center_dist 0))
  **  (IntArray.missing_i d v 0 nv center_dist )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
.

Definition solver_partial_solve_wit_28 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : ((Znth v center_dist 0) <= k_pre)) (PreH2 : (v < nv)) (PreH3 : (ok <> 0)) (PreH4 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH5 : (BFSResult nv edges a second_parent second_dist b )) (PreH6 : (GraphPre nv edges )) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH10 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH11 : (ec = ((2 * nv ) - 2 ))) (PreH12 : (0 <= v)) (PreH13 : (v <= nv)) (PreH14 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full d nv center_dist )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
|--
  “ ((Znth v center_dist 0) <= k_pre) ” 
  &&  “ (v < nv) ” 
  &&  “ (ok <> 0) ” 
  &&  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok ) ”
  &&  (((d + (v * sizeof(INT)))) # Int  |-> (Znth v center_dist 0))
  **  (IntArray.missing_i d v 0 nv center_dist )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
.

Definition solver_partial_solve_wit_29 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : ((Znth v center_dist 0) = k_pre)) (PreH2 : ((Znth v center_dist 0) <= k_pre)) (PreH3 : (v < nv)) (PreH4 : (ok <> 0)) (PreH5 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH6 : (BFSResult nv edges a second_parent second_dist b )) (PreH7 : (GraphPre nv edges )) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 1000000000)) (PreH10 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH11 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH12 : (ec = ((2 * nv ) - 2 ))) (PreH13 : (0 <= v)) (PreH14 : (v <= nv)) (PreH15 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full d nv center_dist )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
|--
  “ ((Znth v center_dist 0) = k_pre) ” 
  &&  “ ((Znth v center_dist 0) <= k_pre) ” 
  &&  “ (v < nv) ” 
  &&  “ (ok <> 0) ” 
  &&  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok ) ”
  &&  (((deg_p + (v * sizeof(INT)))) # Int  |-> (Znth v degree_data 0))
  **  (IntArray.missing_i deg_p v 0 nv degree_data )
  **  (IntArray.full d nv center_dist )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full p nv center_parent )
.

Definition solver_partial_solve_wit_30 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : ((Znth v center_dist 0) <> k_pre)) (PreH2 : ((Znth v center_dist 0) <= k_pre)) (PreH3 : (v < nv)) (PreH4 : (ok <> 0)) (PreH5 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH6 : (BFSResult nv edges a second_parent second_dist b )) (PreH7 : (GraphPre nv edges )) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 1000000000)) (PreH10 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH11 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH12 : (ec = ((2 * nv ) - 2 ))) (PreH13 : (0 <= v)) (PreH14 : (v <= nv)) (PreH15 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full d nv center_dist )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
|--
  “ ((Znth v center_dist 0) <> k_pre) ” 
  &&  “ ((Znth v center_dist 0) <= k_pre) ” 
  &&  “ (v < nv) ” 
  &&  “ (ok <> 0) ” 
  &&  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok ) ”
  &&  (((d + (v * sizeof(INT)))) # Int  |-> (Znth v center_dist 0))
  **  (IntArray.missing_i d v 0 nv center_dist )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
.

Definition solver_partial_solve_wit_31 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : ((Znth v degree_data 0) = 1)) (PreH2 : ((Znth v center_dist 0) = k_pre)) (PreH3 : ((Znth v center_dist 0) <= k_pre)) (PreH4 : (v < nv)) (PreH5 : (ok <> 0)) (PreH6 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH7 : (BFSResult nv edges a second_parent second_dist b )) (PreH8 : (GraphPre nv edges )) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 1000000000)) (PreH11 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH12 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH13 : (ec = ((2 * nv ) - 2 ))) (PreH14 : (0 <= v)) (PreH15 : (v <= nv)) (PreH16 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full d nv center_dist )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full p nv center_parent )
|--
  “ ((Znth v degree_data 0) = 1) ” 
  &&  “ ((Znth v center_dist 0) = k_pre) ” 
  &&  “ ((Znth v center_dist 0) <= k_pre) ” 
  &&  “ (v < nv) ” 
  &&  “ (ok <> 0) ” 
  &&  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok ) ”
  &&  (((d + (v * sizeof(INT)))) # Int  |-> (Znth v center_dist 0))
  **  (IntArray.missing_i d v 0 nv center_dist )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full p nv center_parent )
.

Definition solver_partial_solve_wit_32 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : (v = center)) (PreH2 : ((Znth v center_dist 0) < k_pre)) (PreH3 : ((Znth v center_dist 0) <> k_pre)) (PreH4 : ((Znth v center_dist 0) <= k_pre)) (PreH5 : (v < nv)) (PreH6 : (ok <> 0)) (PreH7 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH8 : (BFSResult nv edges a second_parent second_dist b )) (PreH9 : (GraphPre nv edges )) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 1000000000)) (PreH12 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH13 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH14 : (ec = ((2 * nv ) - 2 ))) (PreH15 : (0 <= v)) (PreH16 : (v <= nv)) (PreH17 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full d nv center_dist )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
|--
  “ (v = center) ” 
  &&  “ ((Znth v center_dist 0) < k_pre) ” 
  &&  “ ((Znth v center_dist 0) <> k_pre) ” 
  &&  “ ((Znth v center_dist 0) <= k_pre) ” 
  &&  “ (v < nv) ” 
  &&  “ (ok <> 0) ” 
  &&  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok ) ”
  &&  (((deg_p + (v * sizeof(INT)))) # Int  |-> (Znth v degree_data 0))
  **  (IntArray.missing_i deg_p v 0 nv degree_data )
  **  (IntArray.full d nv center_dist )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full p nv center_parent )
.

Definition solver_partial_solve_wit_33 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (d: Z) (p: Z) (deg_p: Z) (next_p: Z) (to_p: Z) (head_p: Z) (center: Z) (center_parent: (@list Z)) (center_dist: (@list Z)) (ok: Z) (v: Z) (ec: Z) (degree_data: (@list Z)) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (b: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (a: Z) (PreH1 : (v <> center)) (PreH2 : (v <> center)) (PreH3 : ((Znth v center_dist 0) < k_pre)) (PreH4 : ((Znth v center_dist 0) <> k_pre)) (PreH5 : ((Znth v center_dist 0) <= k_pre)) (PreH6 : (v < nv)) (PreH7 : (ok <> 0)) (PreH8 : (BFSResult nv edges 0 first_parent first_dist a )) (PreH9 : (BFSResult nv edges a second_parent second_dist b )) (PreH10 : (GraphPre nv edges )) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (AdjacencyModel nv edges head_data to_data next_data )) (PreH14 : (DegreePrefix nv edges (nv - 1 ) degree_data )) (PreH15 : (ec = ((2 * nv ) - 2 ))) (PreH16 : (0 <= v)) (PreH17 : (v <= nv)) (PreH18 : (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok )) ,
  (IntArray.full d nv center_dist )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
|--
  “ (v <> center) ” 
  &&  “ (v <> center) ” 
  &&  “ ((Znth v center_dist 0) < k_pre) ” 
  &&  “ ((Znth v center_dist 0) <> k_pre) ” 
  &&  “ ((Znth v center_dist 0) <= k_pre) ” 
  &&  “ (v < nv) ” 
  &&  “ (ok <> 0) ” 
  &&  “ (BFSResult nv edges 0 first_parent first_dist a ) ” 
  &&  “ (BFSResult nv edges a second_parent second_dist b ) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ” 
  &&  “ (DegreePrefix nv edges (nv - 1 ) degree_data ) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= nv) ” 
  &&  “ (SolverDecision nv k_pre edges second_parent second_dist b center center_parent center_dist degree_data v ok ) ”
  &&  (((deg_p + (v * sizeof(INT)))) # Int  |-> (Znth v degree_data 0))
  **  (IntArray.missing_i deg_p v 0 nv degree_data )
  **  (IntArray.full d nv center_dist )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full p nv center_parent )
.

Definition solver_partial_solve_wit_34_pure := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (GraphPre nv edges )) (PreH5 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH6 : (Spec nv k_pre edges ok )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ ((Zlength (head_data)) = nv) ” 
  &&  “ (0 <= nv) ”
) \/
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (a <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (center <= INT_MAX)) (PreH6 : (ok <= INT_MAX)) (PreH7 : (ec <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (a >= INT_MIN)) (PreH10 : (b >= INT_MIN)) (PreH11 : (center >= INT_MIN)) (PreH12 : (ok >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (nv >= INT_MIN)) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 1000000000)) (PreH17 : (ec = ((2 * nv ) - 2 ))) (PreH18 : (GraphPre nv edges )) (PreH19 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH20 : (Spec nv k_pre edges ok )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ (0 <= nv) ” 
  &&  “ ((Zlength (head_data)) = nv) ”
).

Definition solver_partial_solve_wit_34_pure_split_goal_1 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (a <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (center <= INT_MAX)) (PreH6 : (ok <= INT_MAX)) (PreH7 : (ec <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (a >= INT_MIN)) (PreH10 : (b >= INT_MIN)) (PreH11 : (center >= INT_MIN)) (PreH12 : (ok >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (nv >= INT_MIN)) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 1000000000)) (PreH17 : (ec = ((2 * nv ) - 2 ))) (PreH18 : (GraphPre nv edges )) (PreH19 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH20 : (Spec nv k_pre edges ok )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ (0 <= nv) ”
.

Definition solver_partial_solve_wit_34_pure_split_goal_2 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (a <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (center <= INT_MAX)) (PreH6 : (ok <= INT_MAX)) (PreH7 : (ec <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (a >= INT_MIN)) (PreH10 : (b >= INT_MIN)) (PreH11 : (center >= INT_MIN)) (PreH12 : (ok >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (nv >= INT_MIN)) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 1000000000)) (PreH17 : (ec = ((2 * nv ) - 2 ))) (PreH18 : (GraphPre nv edges )) (PreH19 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH20 : (Spec nv k_pre edges ok )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ ((Zlength (head_data)) = nv) ”
.

Definition solver_partial_solve_wit_34_aux := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (GraphPre nv edges )) (PreH5 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH6 : (Spec nv k_pre edges ok )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full head_p nv head_data )
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
|--
  “ ((Zlength (head_data)) = nv) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok ) ” 
  &&  “ (Spec nv k_pre edges ok ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  (IntArray.full head_p nv head_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
.

Definition solver_partial_solve_wit_34 := solver_partial_solve_wit_34_pure -> solver_partial_solve_wit_34_aux.

Definition solver_partial_solve_wit_35_pure := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (GraphPre nv edges )) (PreH5 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH6 : (Spec nv k_pre edges ok )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= ((2 * nv ) - 2 )) ”
) \/
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (a <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (center <= INT_MAX)) (PreH6 : (ok <= INT_MAX)) (PreH7 : (ec <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (a >= INT_MIN)) (PreH10 : (b >= INT_MIN)) (PreH11 : (center >= INT_MIN)) (PreH12 : (ok >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (nv >= INT_MIN)) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 1000000000)) (PreH17 : (ec = ((2 * nv ) - 2 ))) (PreH18 : (GraphPre nv edges )) (PreH19 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH20 : (Spec nv k_pre edges ok )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ (0 <= ((2 * nv ) - 2 )) ” 
  &&  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
).

Definition solver_partial_solve_wit_35_pure_split_goal_1 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (a <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (center <= INT_MAX)) (PreH6 : (ok <= INT_MAX)) (PreH7 : (ec <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (a >= INT_MIN)) (PreH10 : (b >= INT_MIN)) (PreH11 : (center >= INT_MIN)) (PreH12 : (ok >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (nv >= INT_MIN)) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 1000000000)) (PreH17 : (ec = ((2 * nv ) - 2 ))) (PreH18 : (GraphPre nv edges )) (PreH19 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH20 : (Spec nv k_pre edges ok )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ (0 <= ((2 * nv ) - 2 )) ”
.

Definition solver_partial_solve_wit_35_pure_split_goal_2 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (a <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (center <= INT_MAX)) (PreH6 : (ok <= INT_MAX)) (PreH7 : (ec <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (a >= INT_MIN)) (PreH10 : (b >= INT_MIN)) (PreH11 : (center >= INT_MIN)) (PreH12 : (ok >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (nv >= INT_MIN)) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 1000000000)) (PreH17 : (ec = ((2 * nv ) - 2 ))) (PreH18 : (GraphPre nv edges )) (PreH19 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH20 : (Spec nv k_pre edges ok )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ”
.

Definition solver_partial_solve_wit_35_aux := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (GraphPre nv edges )) (PreH5 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH6 : (Spec nv k_pre edges ok )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
|--
  “ ((Zlength (to_data)) = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok ) ” 
  &&  “ (Spec nv k_pre edges ok ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  (IntArray.full to_p ((2 * nv ) - 2 ) to_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
.

Definition solver_partial_solve_wit_35 := solver_partial_solve_wit_35_pure -> solver_partial_solve_wit_35_aux.

Definition solver_partial_solve_wit_36_pure := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (GraphPre nv edges )) (PreH5 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH6 : (Spec nv k_pre edges ok )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= ((2 * nv ) - 2 )) ”
) \/
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (a <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (center <= INT_MAX)) (PreH6 : (ok <= INT_MAX)) (PreH7 : (ec <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (a >= INT_MIN)) (PreH10 : (b >= INT_MIN)) (PreH11 : (center >= INT_MIN)) (PreH12 : (ok >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (nv >= INT_MIN)) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 1000000000)) (PreH17 : (ec = ((2 * nv ) - 2 ))) (PreH18 : (GraphPre nv edges )) (PreH19 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH20 : (Spec nv k_pre edges ok )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ (0 <= ((2 * nv ) - 2 )) ” 
  &&  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
).

Definition solver_partial_solve_wit_36_pure_split_goal_1 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (a <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (center <= INT_MAX)) (PreH6 : (ok <= INT_MAX)) (PreH7 : (ec <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (a >= INT_MIN)) (PreH10 : (b >= INT_MIN)) (PreH11 : (center >= INT_MIN)) (PreH12 : (ok >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (nv >= INT_MIN)) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 1000000000)) (PreH17 : (ec = ((2 * nv ) - 2 ))) (PreH18 : (GraphPre nv edges )) (PreH19 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH20 : (Spec nv k_pre edges ok )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ (0 <= ((2 * nv ) - 2 )) ”
.

Definition solver_partial_solve_wit_36_pure_split_goal_2 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (a <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (center <= INT_MAX)) (PreH6 : (ok <= INT_MAX)) (PreH7 : (ec <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (a >= INT_MIN)) (PreH10 : (b >= INT_MIN)) (PreH11 : (center >= INT_MIN)) (PreH12 : (ok >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (nv >= INT_MIN)) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 1000000000)) (PreH17 : (ec = ((2 * nv ) - 2 ))) (PreH18 : (GraphPre nv edges )) (PreH19 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH20 : (Spec nv k_pre edges ok )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ”
.

Definition solver_partial_solve_wit_36_aux := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (GraphPre nv edges )) (PreH5 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH6 : (Spec nv k_pre edges ok )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
|--
  “ ((Zlength (next_data)) = ((2 * nv ) - 2 )) ” 
  &&  “ (0 <= ((2 * nv ) - 2 )) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok ) ” 
  &&  “ (Spec nv k_pre edges ok ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  (IntArray.full next_p ((2 * nv ) - 2 ) next_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
.

Definition solver_partial_solve_wit_36 := solver_partial_solve_wit_36_pure -> solver_partial_solve_wit_36_aux.

Definition solver_partial_solve_wit_37_pure := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (GraphPre nv edges )) (PreH5 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH6 : (Spec nv k_pre edges ok )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ ((Zlength (degree_data)) = nv) ” 
  &&  “ (0 <= nv) ”
) \/
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (a <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (center <= INT_MAX)) (PreH6 : (ok <= INT_MAX)) (PreH7 : (ec <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (a >= INT_MIN)) (PreH10 : (b >= INT_MIN)) (PreH11 : (center >= INT_MIN)) (PreH12 : (ok >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (nv >= INT_MIN)) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 1000000000)) (PreH17 : (ec = ((2 * nv ) - 2 ))) (PreH18 : (GraphPre nv edges )) (PreH19 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH20 : (Spec nv k_pre edges ok )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ (0 <= nv) ” 
  &&  “ ((Zlength (degree_data)) = nv) ”
).

Definition solver_partial_solve_wit_37_pure_split_goal_1 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (a <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (center <= INT_MAX)) (PreH6 : (ok <= INT_MAX)) (PreH7 : (ec <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (a >= INT_MIN)) (PreH10 : (b >= INT_MIN)) (PreH11 : (center >= INT_MIN)) (PreH12 : (ok >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (nv >= INT_MIN)) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 1000000000)) (PreH17 : (ec = ((2 * nv ) - 2 ))) (PreH18 : (GraphPre nv edges )) (PreH19 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH20 : (Spec nv k_pre edges ok )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ (0 <= nv) ”
.

Definition solver_partial_solve_wit_37_pure_split_goal_2 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (a <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (center <= INT_MAX)) (PreH6 : (ok <= INT_MAX)) (PreH7 : (ec <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (a >= INT_MIN)) (PreH10 : (b >= INT_MIN)) (PreH11 : (center >= INT_MIN)) (PreH12 : (ok >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (nv >= INT_MIN)) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 1000000000)) (PreH17 : (ec = ((2 * nv ) - 2 ))) (PreH18 : (GraphPre nv edges )) (PreH19 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH20 : (Spec nv k_pre edges ok )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ ((Zlength (degree_data)) = nv) ”
.

Definition solver_partial_solve_wit_37_aux := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (GraphPre nv edges )) (PreH5 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH6 : (Spec nv k_pre edges ok )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
|--
  “ ((Zlength (degree_data)) = nv) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok ) ” 
  &&  “ (Spec nv k_pre edges ok ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  (IntArray.full deg_p nv degree_data )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
.

Definition solver_partial_solve_wit_37 := solver_partial_solve_wit_37_pure -> solver_partial_solve_wit_37_aux.

Definition solver_partial_solve_wit_38_pure := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (GraphPre nv edges )) (PreH5 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH6 : (Spec nv k_pre edges ok )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ ((Zlength (center_parent)) = nv) ” 
  &&  “ (0 <= nv) ”
) \/
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (a <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (center <= INT_MAX)) (PreH6 : (ok <= INT_MAX)) (PreH7 : (ec <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (a >= INT_MIN)) (PreH10 : (b >= INT_MIN)) (PreH11 : (center >= INT_MIN)) (PreH12 : (ok >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (nv >= INT_MIN)) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 1000000000)) (PreH17 : (ec = ((2 * nv ) - 2 ))) (PreH18 : (GraphPre nv edges )) (PreH19 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH20 : (Spec nv k_pre edges ok )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ (0 <= nv) ” 
  &&  “ ((Zlength (center_parent)) = nv) ”
).

Definition solver_partial_solve_wit_38_pure_split_goal_1 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (a <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (center <= INT_MAX)) (PreH6 : (ok <= INT_MAX)) (PreH7 : (ec <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (a >= INT_MIN)) (PreH10 : (b >= INT_MIN)) (PreH11 : (center >= INT_MIN)) (PreH12 : (ok >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (nv >= INT_MIN)) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 1000000000)) (PreH17 : (ec = ((2 * nv ) - 2 ))) (PreH18 : (GraphPre nv edges )) (PreH19 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH20 : (Spec nv k_pre edges ok )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ (0 <= nv) ”
.

Definition solver_partial_solve_wit_38_pure_split_goal_2 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (a <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (center <= INT_MAX)) (PreH6 : (ok <= INT_MAX)) (PreH7 : (ec <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (a >= INT_MIN)) (PreH10 : (b >= INT_MIN)) (PreH11 : (center >= INT_MIN)) (PreH12 : (ok >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (nv >= INT_MIN)) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 1000000000)) (PreH17 : (ec = ((2 * nv ) - 2 ))) (PreH18 : (GraphPre nv edges )) (PreH19 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH20 : (Spec nv k_pre edges ok )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p nv center_parent )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ ((Zlength (center_parent)) = nv) ”
.

Definition solver_partial_solve_wit_38_aux := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (GraphPre nv edges )) (PreH5 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH6 : (Spec nv k_pre edges ok )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full p nv center_parent )
  **  (IntArray.full d nv center_dist )
|--
  “ ((Zlength (center_parent)) = nv) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok ) ” 
  &&  “ (Spec nv k_pre edges ok ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  (IntArray.full p nv center_parent )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full d nv center_dist )
.

Definition solver_partial_solve_wit_38 := solver_partial_solve_wit_38_pure -> solver_partial_solve_wit_38_aux.

Definition solver_partial_solve_wit_39_pure := 
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (GraphPre nv edges )) (PreH5 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH6 : (Spec nv k_pre edges ok )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ ((Zlength (center_dist)) = nv) ” 
  &&  “ (0 <= nv) ”
) \/
(
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (a <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (center <= INT_MAX)) (PreH6 : (ok <= INT_MAX)) (PreH7 : (ec <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (a >= INT_MIN)) (PreH10 : (b >= INT_MIN)) (PreH11 : (center >= INT_MIN)) (PreH12 : (ok >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (nv >= INT_MIN)) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 1000000000)) (PreH17 : (ec = ((2 * nv ) - 2 ))) (PreH18 : (GraphPre nv edges )) (PreH19 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH20 : (Spec nv k_pre edges ok )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ (0 <= nv) ” 
  &&  “ ((Zlength (center_dist)) = nv) ”
).

Definition solver_partial_solve_wit_39_pure_split_goal_1 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (a <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (center <= INT_MAX)) (PreH6 : (ok <= INT_MAX)) (PreH7 : (ec <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (a >= INT_MIN)) (PreH10 : (b >= INT_MIN)) (PreH11 : (center >= INT_MIN)) (PreH12 : (ok >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (nv >= INT_MIN)) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 1000000000)) (PreH17 : (ec = ((2 * nv ) - 2 ))) (PreH18 : (GraphPre nv edges )) (PreH19 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH20 : (Spec nv k_pre edges ok )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ (0 <= nv) ”
.

Definition solver_partial_solve_wit_39_pure_split_goal_2 := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (p: Z) (d: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (a <= INT_MAX)) (PreH4 : (b <= INT_MAX)) (PreH5 : (center <= INT_MAX)) (PreH6 : (ok <= INT_MAX)) (PreH7 : (ec <= INT_MAX)) (PreH8 : (nv <= INT_MAX)) (PreH9 : (a >= INT_MIN)) (PreH10 : (b >= INT_MIN)) (PreH11 : (center >= INT_MIN)) (PreH12 : (ok >= INT_MIN)) (PreH13 : (ec >= INT_MIN)) (PreH14 : (nv >= INT_MIN)) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 1000000000)) (PreH17 : (ec = ((2 * nv ) - 2 ))) (PreH18 : (GraphPre nv edges )) (PreH19 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH20 : (Spec nv k_pre edges ok )) (PreH21 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  ((( &( "nn" ) )) # Int  |-> nv)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "ec" ) )) # Int  |-> ec)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "center" ) )) # Int  |-> center)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (IntArray.full d nv center_dist )
|--
  “ ((Zlength (center_dist)) = nv) ”
.

Definition solver_partial_solve_wit_39_aux := 
forall (ev_pre: Z) (eu_pre: Z) (k_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (edges: (@list (Z * Z))) (nv: Z) (first_parent: (@list Z)) (first_dist: (@list Z)) (second_parent: (@list Z)) (second_dist: (@list Z)) (center_parent: (@list Z)) (center_dist: (@list Z)) (head_p: Z) (to_p: Z) (next_p: Z) (deg_p: Z) (head_data: (@list Z)) (to_data: (@list Z)) (next_data: (@list Z)) (degree_data: (@list Z)) (ec: Z) (ok: Z) (center: Z) (b: Z) (a: Z) (d: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 1000000000)) (PreH3 : (ec = ((2 * nv ) - 2 ))) (PreH4 : (GraphPre nv edges )) (PreH5 : (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok )) (PreH6 : (Spec nv k_pre edges ok )) (PreH7 : (AdjacencyModel nv edges head_data to_data next_data )) ,
  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
  **  (IntArray.full d nv center_dist )
|--
  “ ((Zlength (center_dist)) = nv) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (ec = ((2 * nv ) - 2 )) ” 
  &&  “ (GraphPre nv edges ) ” 
  &&  “ (SolverCertificate nv k_pre edges first_parent first_dist a second_parent second_dist b center center_parent center_dist degree_data ok ) ” 
  &&  “ (Spec nv k_pre edges ok ) ” 
  &&  “ (AdjacencyModel nv edges head_data to_data next_data ) ”
  &&  (IntArray.full d nv center_dist )
  **  (IntArray.full eu_pre (nv - 1 ) eu_data )
  **  (IntArray.full ev_pre (nv - 1 ) ev_data )
  **  ((( &( "n" ) )) # Int  |-> nv)
  **  ((( &( "head" ) )) # Ptr  |-> head_p)
  **  ((( &( "to" ) )) # Ptr  |-> to_p)
  **  ((( &( "nxt" ) )) # Ptr  |-> next_p)
  **  ((( &( "deg" ) )) # Ptr  |-> deg_p)
.

Definition solver_partial_solve_wit_39 := solver_partial_solve_wit_39_pure -> solver_partial_solve_wit_39_aux.

Module Type VC_Correct.


Axiom proof_of_bfs_safety_wit_1 : bfs_safety_wit_1.
Axiom proof_of_bfs_safety_wit_2 : bfs_safety_wit_2.
Axiom proof_of_bfs_safety_wit_3 : bfs_safety_wit_3.
Axiom proof_of_bfs_safety_wit_4 : bfs_safety_wit_4.
Axiom proof_of_bfs_safety_wit_5 : bfs_safety_wit_5.
Axiom proof_of_bfs_safety_wit_6 : bfs_safety_wit_6.
Axiom proof_of_bfs_safety_wit_7 : bfs_safety_wit_7.
Axiom proof_of_bfs_safety_wit_8 : bfs_safety_wit_8.
Axiom proof_of_bfs_safety_wit_9 : bfs_safety_wit_9.
Axiom proof_of_bfs_safety_wit_10 : bfs_safety_wit_10.
Axiom proof_of_bfs_safety_wit_11 : bfs_safety_wit_11.
Axiom proof_of_bfs_safety_wit_12 : bfs_safety_wit_12.
Axiom proof_of_bfs_safety_wit_13 : bfs_safety_wit_13.
Axiom proof_of_bfs_safety_wit_14 : bfs_safety_wit_14.
Axiom proof_of_bfs_safety_wit_15 : bfs_safety_wit_15.
Axiom proof_of_bfs_safety_wit_16 : bfs_safety_wit_16.
Axiom proof_of_bfs_safety_wit_17 : bfs_safety_wit_17.
Axiom proof_of_bfs_entail_wit_1 : bfs_entail_wit_1.
Axiom proof_of_bfs_entail_wit_2 : bfs_entail_wit_2.
Axiom proof_of_bfs_entail_wit_3 : bfs_entail_wit_3.
Axiom proof_of_bfs_entail_wit_4_1 : bfs_entail_wit_4_1.
Axiom proof_of_bfs_entail_wit_4_2 : bfs_entail_wit_4_2.
Axiom proof_of_bfs_entail_wit_5_1 : bfs_entail_wit_5_1.
Axiom proof_of_bfs_entail_wit_5_2 : bfs_entail_wit_5_2.
Axiom proof_of_bfs_entail_wit_6 : bfs_entail_wit_6.
Axiom proof_of_bfs_entail_wit_7 : bfs_entail_wit_7.
Axiom proof_of_bfs_return_wit_1 : bfs_return_wit_1.
Axiom proof_of_bfs_partial_solve_wit_1_pure : bfs_partial_solve_wit_1_pure.
Axiom proof_of_bfs_partial_solve_wit_1 : bfs_partial_solve_wit_1.
Axiom proof_of_bfs_partial_solve_wit_2 : bfs_partial_solve_wit_2.
Axiom proof_of_bfs_partial_solve_wit_3 : bfs_partial_solve_wit_3.
Axiom proof_of_bfs_partial_solve_wit_4 : bfs_partial_solve_wit_4.
Axiom proof_of_bfs_partial_solve_wit_5 : bfs_partial_solve_wit_5.
Axiom proof_of_bfs_partial_solve_wit_6 : bfs_partial_solve_wit_6.
Axiom proof_of_bfs_partial_solve_wit_7 : bfs_partial_solve_wit_7.
Axiom proof_of_bfs_partial_solve_wit_8 : bfs_partial_solve_wit_8.
Axiom proof_of_bfs_partial_solve_wit_9 : bfs_partial_solve_wit_9.
Axiom proof_of_bfs_partial_solve_wit_10 : bfs_partial_solve_wit_10.
Axiom proof_of_bfs_partial_solve_wit_11 : bfs_partial_solve_wit_11.
Axiom proof_of_bfs_partial_solve_wit_12 : bfs_partial_solve_wit_12.
Axiom proof_of_bfs_partial_solve_wit_13 : bfs_partial_solve_wit_13.
Axiom proof_of_bfs_partial_solve_wit_14 : bfs_partial_solve_wit_14.
Axiom proof_of_bfs_partial_solve_wit_15 : bfs_partial_solve_wit_15.
Axiom proof_of_bfs_partial_solve_wit_16 : bfs_partial_solve_wit_16.
Axiom proof_of_bfs_partial_solve_wit_17 : bfs_partial_solve_wit_17.
Axiom proof_of_bfs_partial_solve_wit_18 : bfs_partial_solve_wit_18.
Axiom proof_of_bfs_partial_solve_wit_19 : bfs_partial_solve_wit_19.
Axiom proof_of_bfs_partial_solve_wit_20 : bfs_partial_solve_wit_20.
Axiom proof_of_bfs_partial_solve_wit_21 : bfs_partial_solve_wit_21.
Axiom proof_of_bfs_partial_solve_wit_22_pure : bfs_partial_solve_wit_22_pure.
Axiom proof_of_bfs_partial_solve_wit_22 : bfs_partial_solve_wit_22.
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
Axiom proof_of_solver_safety_wit_43 : solver_safety_wit_43.
Axiom proof_of_solver_safety_wit_44 : solver_safety_wit_44.
Axiom proof_of_solver_safety_wit_45 : solver_safety_wit_45.
Axiom proof_of_solver_safety_wit_46 : solver_safety_wit_46.
Axiom proof_of_solver_safety_wit_47 : solver_safety_wit_47.
Axiom proof_of_solver_safety_wit_48 : solver_safety_wit_48.
Axiom proof_of_solver_safety_wit_49 : solver_safety_wit_49.
Axiom proof_of_solver_safety_wit_50 : solver_safety_wit_50.
Axiom proof_of_solver_safety_wit_51 : solver_safety_wit_51.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1.
Axiom proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Axiom proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Axiom proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Axiom proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Axiom proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Axiom proof_of_solver_entail_wit_13_1 : solver_entail_wit_13_1.
Axiom proof_of_solver_entail_wit_13_2 : solver_entail_wit_13_2.
Axiom proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Axiom proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Axiom proof_of_solver_entail_wit_14_3 : solver_entail_wit_14_3.
Axiom proof_of_solver_entail_wit_14_4 : solver_entail_wit_14_4.
Axiom proof_of_solver_entail_wit_14_5 : solver_entail_wit_14_5.
Axiom proof_of_solver_entail_wit_14_6 : solver_entail_wit_14_6.
Axiom proof_of_solver_entail_wit_14_7 : solver_entail_wit_14_7.
Axiom proof_of_solver_entail_wit_15_1 : solver_entail_wit_15_1.
Axiom proof_of_solver_entail_wit_15_2 : solver_entail_wit_15_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
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
Axiom proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15.
Axiom proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16.
Axiom proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17.
Axiom proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18.
Axiom proof_of_solver_partial_solve_wit_19 : solver_partial_solve_wit_19.
Axiom proof_of_solver_partial_solve_wit_20_pure : solver_partial_solve_wit_20_pure.
Axiom proof_of_solver_partial_solve_wit_20 : solver_partial_solve_wit_20.
Axiom proof_of_solver_partial_solve_wit_21_pure : solver_partial_solve_wit_21_pure.
Axiom proof_of_solver_partial_solve_wit_21 : solver_partial_solve_wit_21.
Axiom proof_of_solver_partial_solve_wit_22_pure : solver_partial_solve_wit_22_pure.
Axiom proof_of_solver_partial_solve_wit_22 : solver_partial_solve_wit_22.
Axiom proof_of_solver_partial_solve_wit_23_pure : solver_partial_solve_wit_23_pure.
Axiom proof_of_solver_partial_solve_wit_23 : solver_partial_solve_wit_23.
Axiom proof_of_solver_partial_solve_wit_24 : solver_partial_solve_wit_24.
Axiom proof_of_solver_partial_solve_wit_25 : solver_partial_solve_wit_25.
Axiom proof_of_solver_partial_solve_wit_26_pure : solver_partial_solve_wit_26_pure.
Axiom proof_of_solver_partial_solve_wit_26 : solver_partial_solve_wit_26.
Axiom proof_of_solver_partial_solve_wit_27 : solver_partial_solve_wit_27.
Axiom proof_of_solver_partial_solve_wit_28 : solver_partial_solve_wit_28.
Axiom proof_of_solver_partial_solve_wit_29 : solver_partial_solve_wit_29.
Axiom proof_of_solver_partial_solve_wit_30 : solver_partial_solve_wit_30.
Axiom proof_of_solver_partial_solve_wit_31 : solver_partial_solve_wit_31.
Axiom proof_of_solver_partial_solve_wit_32 : solver_partial_solve_wit_32.
Axiom proof_of_solver_partial_solve_wit_33 : solver_partial_solve_wit_33.
Axiom proof_of_solver_partial_solve_wit_34_pure : solver_partial_solve_wit_34_pure.
Axiom proof_of_solver_partial_solve_wit_34 : solver_partial_solve_wit_34.
Axiom proof_of_solver_partial_solve_wit_35_pure : solver_partial_solve_wit_35_pure.
Axiom proof_of_solver_partial_solve_wit_35 : solver_partial_solve_wit_35.
Axiom proof_of_solver_partial_solve_wit_36_pure : solver_partial_solve_wit_36_pure.
Axiom proof_of_solver_partial_solve_wit_36 : solver_partial_solve_wit_36.
Axiom proof_of_solver_partial_solve_wit_37_pure : solver_partial_solve_wit_37_pure.
Axiom proof_of_solver_partial_solve_wit_37 : solver_partial_solve_wit_37.
Axiom proof_of_solver_partial_solve_wit_38_pure : solver_partial_solve_wit_38_pure.
Axiom proof_of_solver_partial_solve_wit_38 : solver_partial_solve_wit_38.
Axiom proof_of_solver_partial_solve_wit_39_pure : solver_partial_solve_wit_39_pure.
Axiom proof_of_solver_partial_solve_wit_39 : solver_partial_solve_wit_39.

End VC_Correct.
