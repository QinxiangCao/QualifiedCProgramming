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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P038_1365C_rotation_matching_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec: (@list Z)) (pb_spec: (@list Z)) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= n_pre)))) (PreH5 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 b 0)) /\ ((Znth i_2 b 0) <= n_pre)))) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (aligned_4 cnt_pre )) (PreH9 : ((Zlength (pa_spec)) = (n_pre + 1 ))) (PreH10 : ((Zlength (pb_spec)) = (n_pre + 1 ))) (PreH11 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> (((Znth (Znth i_3 a 0) pa_spec 0) = i_3) /\ ((Znth (Znth i_3 b 0) pb_spec 0) = i_3)))) ,
  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (UCharArray.undef_full cnt_pre (sizeof(INT) * n_pre ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec: (@list Z)) (pb_spec: (@list Z)) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= n_pre)))) (PreH5 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 b 0)) /\ ((Znth i_2 b 0) <= n_pre)))) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (aligned_4 cnt_pre )) (PreH9 : (PositionTable a pa_spec n_pre )) (PreH10 : (PositionTable b pb_spec n_pre )) ,
  ((( &( "v" ) )) # Int  |->_)
  **  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full cnt_pre n_pre (repeat_Z (0) (n_pre)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_3 := 
(
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (1 <= v)) (PreH8 : (v <= (n_pre + 1 ))) (PreH9 : (PositionTable a pa_spec n_pre )) (PreH10 : (PositionTable b pb_spec n_pre )) (PreH11 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts )) ,
  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full cnt_pre n_pre counts )
|--
  “ (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth v pa_spec 0) - (Znth v pb_spec 0) )) ”
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (1 <= v)) (PreH8 : (v <= (n_pre + 1 ))) (PreH9 : (PositionTable a pa_spec n_pre )) (PreH10 : (PositionTable b pb_spec n_pre )) (PreH11 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts )) ,
  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full cnt_pre n_pre counts )
|--
  “ (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth v pa_spec 0) - (Znth v pb_spec 0) )) ”
).

Definition solver_safety_wit_3_split_goal_1 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (1 <= v)) (PreH8 : (v <= (n_pre + 1 ))) (PreH9 : (PositionTable a pa_spec n_pre )) (PreH10 : (PositionTable b pb_spec n_pre )) (PreH11 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts )) ,
  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full cnt_pre n_pre counts )
|--
  “ (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) <= INT_MAX) ”
.

Definition solver_safety_wit_3_split_goal_2 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (1 <= v)) (PreH8 : (v <= (n_pre + 1 ))) (PreH9 : (PositionTable a pa_spec n_pre )) (PreH10 : (PositionTable b pb_spec n_pre )) (PreH11 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts )) ,
  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full cnt_pre n_pre counts )
|--
  “ ((INT_MIN) <= ((Znth v pa_spec 0) - (Znth v pb_spec 0) )) ”
.

Definition solver_safety_wit_4 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (1 <= v)) (PreH8 : (v <= (n_pre + 1 ))) (PreH9 : (PositionTable a pa_spec n_pre )) (PreH10 : (PositionTable b pb_spec n_pre )) (PreH11 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts )) ,
  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  ((( &( "shift" ) )) # Int  |-> ((Znth v pa_spec 0) - (Znth v pb_spec 0) ))
  **  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full cnt_pre n_pre counts )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (v: Z) (PreH1 : (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) < 0)) (PreH2 : (v <= n_pre)) (PreH3 : (Pre a b )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (1 <= v)) (PreH9 : (v <= (n_pre + 1 ))) (PreH10 : (PositionTable a pa_spec n_pre )) (PreH11 : (PositionTable b pb_spec n_pre )) (PreH12 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts )) ,
  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  ((( &( "shift" ) )) # Int  |-> ((Znth v pa_spec 0) - (Znth v pb_spec 0) ))
  **  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full cnt_pre n_pre counts )
|--
  “ ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre )) ”
.

Definition solver_safety_wit_6 := 
(
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec: (@list Z)) (pb_spec: (@list Z)) (counts: (@list Z)) (v: Z) (shift: Z) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : ((Zlength (b)) = n_pre)) (PreH6 : (1 <= v)) (PreH7 : (v <= n_pre)) (PreH8 : (0 <= shift)) (PreH9 : (shift < n_pre)) (PreH10 : (shift = ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) % ( n_pre ) ))) (PreH11 : (PositionTable a pa_spec n_pre )) (PreH12 : (PositionTable b pb_spec n_pre )) (PreH13 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts )) ,
  (IntArray.full cnt_pre n_pre counts )
  **  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
|--
  “ (((Znth shift counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth shift counts 0) + 1 )) ”
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec: (@list Z)) (pb_spec: (@list Z)) (counts: (@list Z)) (v: Z) (shift: Z) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : ((Zlength (b)) = n_pre)) (PreH6 : (1 <= v)) (PreH7 : (v <= n_pre)) (PreH8 : (0 <= shift)) (PreH9 : (shift < n_pre)) (PreH10 : (shift = ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) % ( n_pre ) ))) (PreH11 : (PositionTable a pa_spec n_pre )) (PreH12 : (PositionTable b pb_spec n_pre )) (PreH13 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts )) ,
  (IntArray.full cnt_pre n_pre counts )
  **  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
|--
  “ (((Znth shift counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth shift counts 0) + 1 )) ”
).

Definition solver_safety_wit_6_split_goal_1 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec: (@list Z)) (pb_spec: (@list Z)) (counts: (@list Z)) (v: Z) (shift: Z) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : ((Zlength (b)) = n_pre)) (PreH6 : (1 <= v)) (PreH7 : (v <= n_pre)) (PreH8 : (0 <= shift)) (PreH9 : (shift < n_pre)) (PreH10 : (shift = ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) % ( n_pre ) ))) (PreH11 : (PositionTable a pa_spec n_pre )) (PreH12 : (PositionTable b pb_spec n_pre )) (PreH13 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts )) ,
  (IntArray.full cnt_pre n_pre counts )
  **  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
|--
  “ (((Znth shift counts 0) + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_6_split_goal_2 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec: (@list Z)) (pb_spec: (@list Z)) (counts: (@list Z)) (v: Z) (shift: Z) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : ((Zlength (b)) = n_pre)) (PreH6 : (1 <= v)) (PreH7 : (v <= n_pre)) (PreH8 : (0 <= shift)) (PreH9 : (shift < n_pre)) (PreH10 : (shift = ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) % ( n_pre ) ))) (PreH11 : (PositionTable a pa_spec n_pre )) (PreH12 : (PositionTable b pb_spec n_pre )) (PreH13 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts )) ,
  (IntArray.full cnt_pre n_pre counts )
  **  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
|--
  “ ((INT_MIN) <= ((Znth shift counts 0) + 1 )) ”
.

Definition solver_safety_wit_7 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec: (@list Z)) (pb_spec: (@list Z)) (counts: (@list Z)) (v: Z) (shift: Z) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : ((Zlength (b)) = n_pre)) (PreH6 : (1 <= v)) (PreH7 : (v <= n_pre)) (PreH8 : (0 <= shift)) (PreH9 : (shift < n_pre)) (PreH10 : (shift = ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) % ( n_pre ) ))) (PreH11 : (PositionTable a pa_spec n_pre )) (PreH12 : (PositionTable b pb_spec n_pre )) (PreH13 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts )) ,
  (IntArray.full cnt_pre n_pre counts )
  **  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_8 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec: (@list Z)) (pb_spec: (@list Z)) (counts: (@list Z)) (v: Z) (shift: Z) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : ((Zlength (b)) = n_pre)) (PreH6 : (1 <= v)) (PreH7 : (v <= n_pre)) (PreH8 : (0 <= shift)) (PreH9 : (shift < n_pre)) (PreH10 : (shift = ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) % ( n_pre ) ))) (PreH11 : (PositionTable a pa_spec n_pre )) (PreH12 : (PositionTable b pb_spec n_pre )) (PreH13 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts )) ,
  (IntArray.full cnt_pre n_pre (replace_Znth (shift) (((Znth shift counts 0) + 1 )) (counts)) )
  **  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (1 <= v)) (PreH8 : (v <= (n_pre + 1 ))) (PreH9 : (PositionTable a pa_spec n_pre )) (PreH10 : (PositionTable b pb_spec n_pre )) (PreH11 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts )) ,
  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full cnt_pre n_pre counts )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (1 <= v)) (PreH8 : (v <= (n_pre + 1 ))) (PreH9 : (PositionTable a pa_spec n_pre )) (PreH10 : (PositionTable b pb_spec n_pre )) (PreH11 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts )) ,
  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |-> 0)
  **  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full cnt_pre n_pre counts )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_11 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (best: Z) (counts: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (s: Z) (PreH1 : ((Znth s counts 0) > best)) (PreH2 : (s < n_pre)) (PreH3 : (Pre a b )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (0 <= s)) (PreH9 : (s <= n_pre)) (PreH10 : (PositionTable a pa_spec n_pre )) (PreH11 : (PositionTable b pb_spec n_pre )) (PreH12 : (RotationTallyPrefix pa_spec pb_spec n_pre (n_pre + 1 ) counts )) (PreH13 : (CountPrefixMaximum counts s best )) ,
  (IntArray.full cnt_pre n_pre counts )
  **  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "best" ) )) # Int  |-> (Znth s counts 0))
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
|--
  “ ((s + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (s + 1 )) ”
.

Definition solver_safety_wit_12 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (best: Z) (counts: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (s: Z) (PreH1 : ((Znth s counts 0) <= best)) (PreH2 : (s < n_pre)) (PreH3 : (Pre a b )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (0 <= s)) (PreH9 : (s <= n_pre)) (PreH10 : (PositionTable a pa_spec n_pre )) (PreH11 : (PositionTable b pb_spec n_pre )) (PreH12 : (RotationTallyPrefix pa_spec pb_spec n_pre (n_pre + 1 ) counts )) (PreH13 : (CountPrefixMaximum counts s best )) ,
  (IntArray.full cnt_pre n_pre counts )
  **  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
|--
  “ ((s + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (s + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 a 0)) /\ ((Znth i_4 a 0) <= n_pre)))) (PreH5 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < n_pre)) -> ((1 <= (Znth i_5 b 0)) /\ ((Znth i_5 b 0) <= n_pre)))) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : ((Zlength (pa_spec_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pb_spec_2)) = (n_pre + 1 ))) (PreH10 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < n_pre)) -> (((Znth (Znth i_6 a 0) pa_spec_2 0) = i_6) /\ ((Znth (Znth i_6 b 0) pb_spec_2 0) = i_6)))) ,
  (IntArray.full pa_pre (n_pre + 1 ) pa_spec_2 )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec_2 )
  **  (IntArray.undef_full cnt_pre n_pre )
|--
  EX (pb_spec: (@list Z))  (pa_spec: (@list Z)) ,
  “ (Pre a b ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= n_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 b 0)) /\ ((Znth i_2 b 0) <= n_pre))) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ ((Zlength (b)) = n_pre) ” 
  &&  “ (aligned_4 cnt_pre ) ” 
  &&  “ ((Zlength (pa_spec)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pb_spec)) = (n_pre + 1 )) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> (((Znth (Znth i_3 a 0) pa_spec 0) = i_3) /\ ((Znth (Znth i_3 b 0) pb_spec 0) = i_3))) ”
  &&  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (UCharArray.undef_full cnt_pre (sizeof(INT) * n_pre ) )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 a 0)) /\ ((Znth i_4 a 0) <= n_pre)))) (PreH5 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < n_pre)) -> ((1 <= (Znth i_5 b 0)) /\ ((Znth i_5 b 0) <= n_pre)))) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : ((Zlength (pa_spec_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pb_spec_2)) = (n_pre + 1 ))) (PreH10 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < n_pre)) -> (((Znth (Znth i_6 a 0) pa_spec_2 0) = i_6) /\ ((Znth (Znth i_6 b 0) pb_spec_2 0) = i_6)))) ,
  (IntArray.undef_full cnt_pre n_pre )
|--
  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> (((Znth (Znth i_3 a 0) pa_spec_2 0) = i_3) /\ ((Znth (Znth i_3 b 0) pb_spec_2 0) = i_3))) ” 
  &&  “ (aligned_4 cnt_pre ) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 b 0)) /\ ((Znth i_2 b 0) <= n_pre))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= n_pre))) ”
  &&  (UCharArray.undef_full cnt_pre (sizeof(INT) * n_pre ) )
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 a 0)) /\ ((Znth i_4 a 0) <= n_pre)))) (PreH5 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < n_pre)) -> ((1 <= (Znth i_5 b 0)) /\ ((Znth i_5 b 0) <= n_pre)))) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : ((Zlength (pa_spec_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pb_spec_2)) = (n_pre + 1 ))) (PreH10 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < n_pre)) -> (((Znth (Znth i_6 a 0) pa_spec_2 0) = i_6) /\ ((Znth (Znth i_6 b 0) pb_spec_2 0) = i_6)))) ,
  (IntArray.undef_full cnt_pre n_pre )
|--
  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> (((Znth (Znth i_3 a 0) pa_spec_2 0) = i_3) /\ ((Znth (Znth i_3 b 0) pb_spec_2 0) = i_3))) ”
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 a 0)) /\ ((Znth i_4 a 0) <= n_pre)))) (PreH5 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < n_pre)) -> ((1 <= (Znth i_5 b 0)) /\ ((Znth i_5 b 0) <= n_pre)))) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : ((Zlength (pa_spec_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pb_spec_2)) = (n_pre + 1 ))) (PreH10 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < n_pre)) -> (((Znth (Znth i_6 a 0) pa_spec_2 0) = i_6) /\ ((Znth (Znth i_6 b 0) pb_spec_2 0) = i_6)))) ,
  (IntArray.undef_full cnt_pre n_pre )
|--
  “ (aligned_4 cnt_pre ) ”
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 a 0)) /\ ((Znth i_4 a 0) <= n_pre)))) (PreH5 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < n_pre)) -> ((1 <= (Znth i_5 b 0)) /\ ((Znth i_5 b 0) <= n_pre)))) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : ((Zlength (pa_spec_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pb_spec_2)) = (n_pre + 1 ))) (PreH10 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < n_pre)) -> (((Znth (Znth i_6 a 0) pa_spec_2 0) = i_6) /\ ((Znth (Znth i_6 b 0) pb_spec_2 0) = i_6)))) ,
  (IntArray.undef_full cnt_pre n_pre )
|--
  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 b 0)) /\ ((Znth i_2 b 0) <= n_pre))) ”
.

Definition solver_entail_wit_1_split_goal_4 := 
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 a 0)) /\ ((Znth i_4 a 0) <= n_pre)))) (PreH5 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < n_pre)) -> ((1 <= (Znth i_5 b 0)) /\ ((Znth i_5 b 0) <= n_pre)))) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : ((Zlength (pa_spec_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pb_spec_2)) = (n_pre + 1 ))) (PreH10 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < n_pre)) -> (((Znth (Znth i_6 a 0) pa_spec_2 0) = i_6) /\ ((Znth (Znth i_6 b 0) pb_spec_2 0) = i_6)))) ,
  (IntArray.undef_full cnt_pre n_pre )
|--
  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= n_pre))) ”
.

Definition solver_entail_wit_1_split_goal_spatial := 
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 a 0)) /\ ((Znth i_4 a 0) <= n_pre)))) (PreH5 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < n_pre)) -> ((1 <= (Znth i_5 b 0)) /\ ((Znth i_5 b 0) <= n_pre)))) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : ((Zlength (pa_spec_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pb_spec_2)) = (n_pre + 1 ))) (PreH10 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < n_pre)) -> (((Znth (Znth i_6 a 0) pa_spec_2 0) = i_6) /\ ((Znth (Znth i_6 b 0) pb_spec_2 0) = i_6)))) ,
  (IntArray.undef_full cnt_pre n_pre )
|--
  (UCharArray.undef_full cnt_pre (sizeof(INT) * n_pre ) )
.

Definition solver_entail_wit_2 := 
(
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (retval: Z) (PreH1 : (retval = cnt_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((1 <= (Znth i_3 a 0)) /\ ((Znth i_3 a 0) <= n_pre)))) (PreH6 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 b 0)) /\ ((Znth i_4 b 0) <= n_pre)))) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : ((Zlength (b)) = n_pre)) (PreH9 : (aligned_4 cnt_pre )) (PreH10 : ((Zlength (pa_spec_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (pb_spec_2)) = (n_pre + 1 ))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < n_pre)) -> (((Znth (Znth i_5 a 0) pa_spec_2 0) = i_5) /\ ((Znth (Znth i_5 b 0) pb_spec_2 0) = i_5)))) ,
  (UCharArray.full cnt_pre (sizeof(INT) * n_pre ) (repeat_Z (0) ((sizeof(INT) * n_pre ))) )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec_2 )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec_2 )
|--
  EX (pb_spec: (@list Z))  (pa_spec: (@list Z)) ,
  “ (Pre a b ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= n_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 b 0)) /\ ((Znth i_2 b 0) <= n_pre))) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ ((Zlength (b)) = n_pre) ” 
  &&  “ (aligned_4 cnt_pre ) ” 
  &&  “ (PositionTable a pa_spec n_pre ) ” 
  &&  “ (PositionTable b pb_spec n_pre ) ”
  &&  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full cnt_pre n_pre (repeat_Z (0) (n_pre)) )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (retval: Z) (PreH1 : (retval = cnt_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((1 <= (Znth i_3 a 0)) /\ ((Znth i_3 a 0) <= n_pre)))) (PreH6 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 b 0)) /\ ((Znth i_4 b 0) <= n_pre)))) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : ((Zlength (b)) = n_pre)) (PreH9 : (aligned_4 cnt_pre )) (PreH10 : ((Zlength (pa_spec_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (pb_spec_2)) = (n_pre + 1 ))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < n_pre)) -> (((Znth (Znth i_5 a 0) pa_spec_2 0) = i_5) /\ ((Znth (Znth i_5 b 0) pb_spec_2 0) = i_5)))) ,
  (UCharArray.full cnt_pre (sizeof(INT) * n_pre ) (repeat_Z (0) ((sizeof(INT) * n_pre ))) )
|--
  “ (PositionTable b pb_spec_2 n_pre ) ” 
  &&  “ (PositionTable a pa_spec_2 n_pre ) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 b 0)) /\ ((Znth i_2 b 0) <= n_pre))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= n_pre))) ”
  &&  (IntArray.full cnt_pre n_pre (repeat_Z (0) (n_pre)) )
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (retval: Z) (PreH1 : (retval = cnt_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((1 <= (Znth i_3 a 0)) /\ ((Znth i_3 a 0) <= n_pre)))) (PreH6 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 b 0)) /\ ((Znth i_4 b 0) <= n_pre)))) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : ((Zlength (b)) = n_pre)) (PreH9 : (aligned_4 cnt_pre )) (PreH10 : ((Zlength (pa_spec_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (pb_spec_2)) = (n_pre + 1 ))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < n_pre)) -> (((Znth (Znth i_5 a 0) pa_spec_2 0) = i_5) /\ ((Znth (Znth i_5 b 0) pb_spec_2 0) = i_5)))) ,
  (UCharArray.full cnt_pre (sizeof(INT) * n_pre ) (repeat_Z (0) ((sizeof(INT) * n_pre ))) )
|--
  “ (PositionTable b pb_spec_2 n_pre ) ”
.

Definition solver_entail_wit_2_split_goal_2 := 
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (retval: Z) (PreH1 : (retval = cnt_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((1 <= (Znth i_3 a 0)) /\ ((Znth i_3 a 0) <= n_pre)))) (PreH6 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 b 0)) /\ ((Znth i_4 b 0) <= n_pre)))) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : ((Zlength (b)) = n_pre)) (PreH9 : (aligned_4 cnt_pre )) (PreH10 : ((Zlength (pa_spec_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (pb_spec_2)) = (n_pre + 1 ))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < n_pre)) -> (((Znth (Znth i_5 a 0) pa_spec_2 0) = i_5) /\ ((Znth (Znth i_5 b 0) pb_spec_2 0) = i_5)))) ,
  (UCharArray.full cnt_pre (sizeof(INT) * n_pre ) (repeat_Z (0) ((sizeof(INT) * n_pre ))) )
|--
  “ (PositionTable a pa_spec_2 n_pre ) ”
.

Definition solver_entail_wit_2_split_goal_3 := 
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (retval: Z) (PreH1 : (retval = cnt_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((1 <= (Znth i_3 a 0)) /\ ((Znth i_3 a 0) <= n_pre)))) (PreH6 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 b 0)) /\ ((Znth i_4 b 0) <= n_pre)))) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : ((Zlength (b)) = n_pre)) (PreH9 : (aligned_4 cnt_pre )) (PreH10 : ((Zlength (pa_spec_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (pb_spec_2)) = (n_pre + 1 ))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < n_pre)) -> (((Znth (Znth i_5 a 0) pa_spec_2 0) = i_5) /\ ((Znth (Znth i_5 b 0) pb_spec_2 0) = i_5)))) ,
  (UCharArray.full cnt_pre (sizeof(INT) * n_pre ) (repeat_Z (0) ((sizeof(INT) * n_pre ))) )
|--
  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 b 0)) /\ ((Znth i_2 b 0) <= n_pre))) ”
.

Definition solver_entail_wit_2_split_goal_4 := 
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (retval: Z) (PreH1 : (retval = cnt_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((1 <= (Znth i_3 a 0)) /\ ((Znth i_3 a 0) <= n_pre)))) (PreH6 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 b 0)) /\ ((Znth i_4 b 0) <= n_pre)))) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : ((Zlength (b)) = n_pre)) (PreH9 : (aligned_4 cnt_pre )) (PreH10 : ((Zlength (pa_spec_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (pb_spec_2)) = (n_pre + 1 ))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < n_pre)) -> (((Znth (Znth i_5 a 0) pa_spec_2 0) = i_5) /\ ((Znth (Znth i_5 b 0) pb_spec_2 0) = i_5)))) ,
  (UCharArray.full cnt_pre (sizeof(INT) * n_pre ) (repeat_Z (0) ((sizeof(INT) * n_pre ))) )
|--
  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= n_pre))) ”
.

Definition solver_entail_wit_2_split_goal_spatial := 
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (retval: Z) (PreH1 : (retval = cnt_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((1 <= (Znth i_3 a 0)) /\ ((Znth i_3 a 0) <= n_pre)))) (PreH6 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 b 0)) /\ ((Znth i_4 b 0) <= n_pre)))) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : ((Zlength (b)) = n_pre)) (PreH9 : (aligned_4 cnt_pre )) (PreH10 : ((Zlength (pa_spec_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (pb_spec_2)) = (n_pre + 1 ))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < n_pre)) -> (((Znth (Znth i_5 a 0) pa_spec_2 0) = i_5) /\ ((Znth (Znth i_5 b 0) pb_spec_2 0) = i_5)))) ,
  (UCharArray.full cnt_pre (sizeof(INT) * n_pre ) (repeat_Z (0) ((sizeof(INT) * n_pre ))) )
|--
  (IntArray.full cnt_pre n_pre (repeat_Z (0) (n_pre)) )
.

Definition solver_entail_wit_3 := 
(
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= n_pre)))) (PreH5 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 b 0)) /\ ((Znth i_2 b 0) <= n_pre)))) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (aligned_4 cnt_pre )) (PreH9 : (PositionTable a pa_spec_2 n_pre )) (PreH10 : (PositionTable b pb_spec_2 n_pre )) ,
  (IntArray.full pa_pre (n_pre + 1 ) pa_spec_2 )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec_2 )
  **  (IntArray.full cnt_pre n_pre (repeat_Z (0) (n_pre)) )
|--
  EX (counts: (@list Z))  (pb_spec: (@list Z))  (pa_spec: (@list Z)) ,
  “ (Pre a b ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ ((Zlength (b)) = n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (PositionTable a pa_spec n_pre ) ” 
  &&  “ (PositionTable b pb_spec n_pre ) ” 
  &&  “ (RotationTallyPrefix pa_spec pb_spec n_pre 1 counts ) ”
  &&  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full cnt_pre n_pre counts )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= n_pre)))) (PreH5 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 b 0)) /\ ((Znth i_2 b 0) <= n_pre)))) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (aligned_4 cnt_pre )) (PreH9 : (PositionTable a pa_spec_2 n_pre )) (PreH10 : (PositionTable b pb_spec_2 n_pre )) ,
  TT && emp 
|--
  “ (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre 1 (repeat_Z (0) (n_pre)) ) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= n_pre)))) (PreH5 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 b 0)) /\ ((Znth i_2 b 0) <= n_pre)))) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (aligned_4 cnt_pre )) (PreH9 : (PositionTable a pa_spec_2 n_pre )) (PreH10 : (PositionTable b pb_spec_2 n_pre )) ,
  (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre 1 (repeat_Z (0) (n_pre)) )
.

Definition solver_entail_wit_4_1 := 
(
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts_2: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (v: Z) (PreH1 : (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) < 0)) (PreH2 : (v <= n_pre)) (PreH3 : (Pre a b )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (1 <= v)) (PreH9 : (v <= (n_pre + 1 ))) (PreH10 : (PositionTable a pa_spec n_pre )) (PreH11 : (PositionTable b pb_spec n_pre )) (PreH12 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts_2 )) ,
  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full cnt_pre n_pre counts_2 )
|--
  EX (counts: (@list Z))  (pb_spec_2: (@list Z))  (pa_spec_2: (@list Z)) ,
  “ (Pre a b ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ ((Zlength (b)) = n_pre) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ (0 <= (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre )) ” 
  &&  “ ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) < n_pre) ” 
  &&  “ ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) = ((((Znth v pa_spec_2 0) - (Znth v pb_spec_2 0) ) + n_pre ) % ( n_pre ) )) ” 
  &&  “ (PositionTable a pa_spec_2 n_pre ) ” 
  &&  “ (PositionTable b pb_spec_2 n_pre ) ” 
  &&  “ (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre v counts ) ”
  &&  (IntArray.full pa_pre (n_pre + 1 ) pa_spec_2 )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec_2 )
  **  (IntArray.full cnt_pre n_pre counts )
) \/
(
forall (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts_2: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (v: Z) (PreH1 : (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) < 0)) (PreH2 : (v <= n_pre)) (PreH3 : (Pre a b )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (1 <= v)) (PreH9 : (v <= (n_pre + 1 ))) (PreH10 : (PositionTable a pa_spec n_pre )) (PreH11 : (PositionTable b pb_spec n_pre )) (PreH12 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts_2 )) ,
  TT && emp 
|--
  “ ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) = ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) % ( n_pre ) )) ” 
  &&  “ (0 <= (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre )) ”
  &&  emp
).

Definition solver_entail_wit_4_1_split_goal_1 := 
forall (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts_2: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (v: Z) (PreH1 : (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) < 0)) (PreH2 : (v <= n_pre)) (PreH3 : (Pre a b )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (1 <= v)) (PreH9 : (v <= (n_pre + 1 ))) (PreH10 : (PositionTable a pa_spec n_pre )) (PreH11 : (PositionTable b pb_spec n_pre )) (PreH12 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts_2 )) ,
  ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) = ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) % ( n_pre ) ))
.

Definition solver_entail_wit_4_1_split_goal_2 := 
forall (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts_2: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (v: Z) (PreH1 : (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) < 0)) (PreH2 : (v <= n_pre)) (PreH3 : (Pre a b )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (1 <= v)) (PreH9 : (v <= (n_pre + 1 ))) (PreH10 : (PositionTable a pa_spec n_pre )) (PreH11 : (PositionTable b pb_spec n_pre )) (PreH12 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts_2 )) ,
  (0 <= (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ))
.

Definition solver_entail_wit_4_2 := 
(
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts_2: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (v: Z) (PreH1 : (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) >= 0)) (PreH2 : (v <= n_pre)) (PreH3 : (Pre a b )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (1 <= v)) (PreH9 : (v <= (n_pre + 1 ))) (PreH10 : (PositionTable a pa_spec n_pre )) (PreH11 : (PositionTable b pb_spec n_pre )) (PreH12 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts_2 )) ,
  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full cnt_pre n_pre counts_2 )
|--
  EX (counts: (@list Z))  (pb_spec_2: (@list Z))  (pa_spec_2: (@list Z)) ,
  “ (Pre a b ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ ((Zlength (b)) = n_pre) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ (0 <= ((Znth v pa_spec 0) - (Znth v pb_spec 0) )) ” 
  &&  “ (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) < n_pre) ” 
  &&  “ (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) = ((((Znth v pa_spec_2 0) - (Znth v pb_spec_2 0) ) + n_pre ) % ( n_pre ) )) ” 
  &&  “ (PositionTable a pa_spec_2 n_pre ) ” 
  &&  “ (PositionTable b pb_spec_2 n_pre ) ” 
  &&  “ (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre v counts ) ”
  &&  (IntArray.full pa_pre (n_pre + 1 ) pa_spec_2 )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec_2 )
  **  (IntArray.full cnt_pre n_pre counts )
) \/
(
forall (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts_2: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (v: Z) (PreH1 : (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) >= 0)) (PreH2 : (v <= n_pre)) (PreH3 : (Pre a b )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (1 <= v)) (PreH9 : (v <= (n_pre + 1 ))) (PreH10 : (PositionTable a pa_spec n_pre )) (PreH11 : (PositionTable b pb_spec n_pre )) (PreH12 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts_2 )) ,
  TT && emp 
|--
  “ (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) = ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) % ( n_pre ) )) ” 
  &&  “ (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) < n_pre) ”
  &&  emp
).

Definition solver_entail_wit_4_2_split_goal_1 := 
forall (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts_2: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (v: Z) (PreH1 : (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) >= 0)) (PreH2 : (v <= n_pre)) (PreH3 : (Pre a b )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (1 <= v)) (PreH9 : (v <= (n_pre + 1 ))) (PreH10 : (PositionTable a pa_spec n_pre )) (PreH11 : (PositionTable b pb_spec n_pre )) (PreH12 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts_2 )) ,
  (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) = ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) % ( n_pre ) ))
.

Definition solver_entail_wit_4_2_split_goal_2 := 
forall (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts_2: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (v: Z) (PreH1 : (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) >= 0)) (PreH2 : (v <= n_pre)) (PreH3 : (Pre a b )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (1 <= v)) (PreH9 : (v <= (n_pre + 1 ))) (PreH10 : (PositionTable a pa_spec n_pre )) (PreH11 : (PositionTable b pb_spec n_pre )) (PreH12 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts_2 )) ,
  (((Znth v pa_spec 0) - (Znth v pb_spec 0) ) < n_pre)
.

Definition solver_entail_wit_5 := 
(
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (counts_2: (@list Z)) (v: Z) (shift: Z) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : ((Zlength (b)) = n_pre)) (PreH6 : (1 <= v)) (PreH7 : (v <= n_pre)) (PreH8 : (0 <= shift)) (PreH9 : (shift < n_pre)) (PreH10 : (shift = ((((Znth v pa_spec_2 0) - (Znth v pb_spec_2 0) ) + n_pre ) % ( n_pre ) ))) (PreH11 : (PositionTable a pa_spec_2 n_pre )) (PreH12 : (PositionTable b pb_spec_2 n_pre )) (PreH13 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre v counts_2 )) ,
  (IntArray.full cnt_pre n_pre (replace_Znth (shift) (((Znth shift counts_2 0) + 1 )) (counts_2)) )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec_2 )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec_2 )
|--
  EX (counts: (@list Z))  (pb_spec: (@list Z))  (pa_spec: (@list Z)) ,
  “ (Pre a b ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ ((Zlength (b)) = n_pre) ” 
  &&  “ (1 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (PositionTable a pa_spec n_pre ) ” 
  &&  “ (PositionTable b pb_spec n_pre ) ” 
  &&  “ (RotationTallyPrefix pa_spec pb_spec n_pre (v + 1 ) counts ) ”
  &&  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full cnt_pre n_pre counts )
) \/
(
forall (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (counts_2: (@list Z)) (v: Z) (shift: Z) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : ((Zlength (b)) = n_pre)) (PreH6 : (1 <= v)) (PreH7 : (v <= n_pre)) (PreH8 : (0 <= shift)) (PreH9 : (shift < n_pre)) (PreH10 : (shift = ((((Znth v pa_spec_2 0) - (Znth v pb_spec_2 0) ) + n_pre ) % ( n_pre ) ))) (PreH11 : (PositionTable a pa_spec_2 n_pre )) (PreH12 : (PositionTable b pb_spec_2 n_pre )) (PreH13 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre v counts_2 )) ,
  TT && emp 
|--
  “ (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre (v + 1 ) (replace_Znth (shift) (((Znth shift counts_2 0) + 1 )) (counts_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec_2: (@list Z)) (pb_spec_2: (@list Z)) (counts_2: (@list Z)) (v: Z) (shift: Z) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : ((Zlength (b)) = n_pre)) (PreH6 : (1 <= v)) (PreH7 : (v <= n_pre)) (PreH8 : (0 <= shift)) (PreH9 : (shift < n_pre)) (PreH10 : (shift = ((((Znth v pa_spec_2 0) - (Znth v pb_spec_2 0) ) + n_pre ) % ( n_pre ) ))) (PreH11 : (PositionTable a pa_spec_2 n_pre )) (PreH12 : (PositionTable b pb_spec_2 n_pre )) (PreH13 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre v counts_2 )) ,
  (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre (v + 1 ) (replace_Znth (shift) (((Znth shift counts_2 0) + 1 )) (counts_2)) )
.

Definition solver_entail_wit_6 := 
(
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts_2: (@list Z)) (pb_spec_2: (@list Z)) (pa_spec_2: (@list Z)) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (1 <= v)) (PreH8 : (v <= (n_pre + 1 ))) (PreH9 : (PositionTable a pa_spec_2 n_pre )) (PreH10 : (PositionTable b pb_spec_2 n_pre )) (PreH11 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre v counts_2 )) ,
  (IntArray.full pa_pre (n_pre + 1 ) pa_spec_2 )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec_2 )
  **  (IntArray.full cnt_pre n_pre counts_2 )
|--
  EX (counts: (@list Z))  (pb_spec: (@list Z))  (pa_spec: (@list Z)) ,
  “ (Pre a b ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ ((Zlength (b)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (PositionTable a pa_spec n_pre ) ” 
  &&  “ (PositionTable b pb_spec n_pre ) ” 
  &&  “ (RotationTallyPrefix pa_spec pb_spec n_pre (n_pre + 1 ) counts ) ” 
  &&  “ (CountPrefixMaximum counts 0 0 ) ”
  &&  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full cnt_pre n_pre counts )
) \/
(
forall (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts_2: (@list Z)) (pb_spec_2: (@list Z)) (pa_spec_2: (@list Z)) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (1 <= v)) (PreH8 : (v <= (n_pre + 1 ))) (PreH9 : (PositionTable a pa_spec_2 n_pre )) (PreH10 : (PositionTable b pb_spec_2 n_pre )) (PreH11 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre v counts_2 )) ,
  TT && emp 
|--
  “ (CountPrefixMaximum counts_2 0 0 ) ” 
  &&  “ (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre (n_pre + 1 ) counts_2 ) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 := 
forall (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts_2: (@list Z)) (pb_spec_2: (@list Z)) (pa_spec_2: (@list Z)) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (1 <= v)) (PreH8 : (v <= (n_pre + 1 ))) (PreH9 : (PositionTable a pa_spec_2 n_pre )) (PreH10 : (PositionTable b pb_spec_2 n_pre )) (PreH11 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre v counts_2 )) ,
  (CountPrefixMaximum counts_2 0 0 )
.

Definition solver_entail_wit_6_split_goal_2 := 
forall (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts_2: (@list Z)) (pb_spec_2: (@list Z)) (pa_spec_2: (@list Z)) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (1 <= v)) (PreH8 : (v <= (n_pre + 1 ))) (PreH9 : (PositionTable a pa_spec_2 n_pre )) (PreH10 : (PositionTable b pb_spec_2 n_pre )) (PreH11 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre v counts_2 )) ,
  (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre (n_pre + 1 ) counts_2 )
.

Definition solver_entail_wit_7_1 := 
(
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (best: Z) (counts_2: (@list Z)) (pb_spec_2: (@list Z)) (pa_spec_2: (@list Z)) (s: Z) (PreH1 : ((Znth s counts_2 0) > best)) (PreH2 : (s < n_pre)) (PreH3 : (Pre a b )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (0 <= s)) (PreH9 : (s <= n_pre)) (PreH10 : (PositionTable a pa_spec_2 n_pre )) (PreH11 : (PositionTable b pb_spec_2 n_pre )) (PreH12 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre (n_pre + 1 ) counts_2 )) (PreH13 : (CountPrefixMaximum counts_2 s best )) ,
  (IntArray.full cnt_pre n_pre counts_2 )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec_2 )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec_2 )
|--
  EX (counts: (@list Z))  (pb_spec: (@list Z))  (pa_spec: (@list Z)) ,
  “ (Pre a b ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ ((Zlength (b)) = n_pre) ” 
  &&  “ (0 <= (s + 1 )) ” 
  &&  “ ((s + 1 ) <= n_pre) ” 
  &&  “ (PositionTable a pa_spec n_pre ) ” 
  &&  “ (PositionTable b pb_spec n_pre ) ” 
  &&  “ (RotationTallyPrefix pa_spec pb_spec n_pre (n_pre + 1 ) counts ) ” 
  &&  “ (CountPrefixMaximum counts (s + 1 ) (Znth s counts_2 0) ) ”
  &&  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full cnt_pre n_pre counts )
) \/
(
forall (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (best: Z) (counts_2: (@list Z)) (pb_spec_2: (@list Z)) (pa_spec_2: (@list Z)) (s: Z) (PreH1 : ((Znth s counts_2 0) > best)) (PreH2 : (s < n_pre)) (PreH3 : (Pre a b )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (0 <= s)) (PreH9 : (s <= n_pre)) (PreH10 : (PositionTable a pa_spec_2 n_pre )) (PreH11 : (PositionTable b pb_spec_2 n_pre )) (PreH12 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre (n_pre + 1 ) counts_2 )) (PreH13 : (CountPrefixMaximum counts_2 s best )) ,
  TT && emp 
|--
  “ (CountPrefixMaximum counts_2 (s + 1 ) (Znth s counts_2 0) ) ”
  &&  emp
).

Definition solver_entail_wit_7_1_split_goal_1 := 
forall (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (best: Z) (counts_2: (@list Z)) (pb_spec_2: (@list Z)) (pa_spec_2: (@list Z)) (s: Z) (PreH1 : ((Znth s counts_2 0) > best)) (PreH2 : (s < n_pre)) (PreH3 : (Pre a b )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (0 <= s)) (PreH9 : (s <= n_pre)) (PreH10 : (PositionTable a pa_spec_2 n_pre )) (PreH11 : (PositionTable b pb_spec_2 n_pre )) (PreH12 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre (n_pre + 1 ) counts_2 )) (PreH13 : (CountPrefixMaximum counts_2 s best )) ,
  (CountPrefixMaximum counts_2 (s + 1 ) (Znth s counts_2 0) )
.

Definition solver_entail_wit_7_2 := 
(
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (best: Z) (counts_2: (@list Z)) (pb_spec_2: (@list Z)) (pa_spec_2: (@list Z)) (s: Z) (PreH1 : ((Znth s counts_2 0) <= best)) (PreH2 : (s < n_pre)) (PreH3 : (Pre a b )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (0 <= s)) (PreH9 : (s <= n_pre)) (PreH10 : (PositionTable a pa_spec_2 n_pre )) (PreH11 : (PositionTable b pb_spec_2 n_pre )) (PreH12 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre (n_pre + 1 ) counts_2 )) (PreH13 : (CountPrefixMaximum counts_2 s best )) ,
  (IntArray.full cnt_pre n_pre counts_2 )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec_2 )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec_2 )
|--
  EX (counts: (@list Z))  (pb_spec: (@list Z))  (pa_spec: (@list Z)) ,
  “ (Pre a b ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ ((Zlength (b)) = n_pre) ” 
  &&  “ (0 <= (s + 1 )) ” 
  &&  “ ((s + 1 ) <= n_pre) ” 
  &&  “ (PositionTable a pa_spec n_pre ) ” 
  &&  “ (PositionTable b pb_spec n_pre ) ” 
  &&  “ (RotationTallyPrefix pa_spec pb_spec n_pre (n_pre + 1 ) counts ) ” 
  &&  “ (CountPrefixMaximum counts (s + 1 ) best ) ”
  &&  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full cnt_pre n_pre counts )
) \/
(
forall (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (best: Z) (counts_2: (@list Z)) (pb_spec_2: (@list Z)) (pa_spec_2: (@list Z)) (s: Z) (PreH1 : ((Znth s counts_2 0) <= best)) (PreH2 : (s < n_pre)) (PreH3 : (Pre a b )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (0 <= s)) (PreH9 : (s <= n_pre)) (PreH10 : (PositionTable a pa_spec_2 n_pre )) (PreH11 : (PositionTable b pb_spec_2 n_pre )) (PreH12 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre (n_pre + 1 ) counts_2 )) (PreH13 : (CountPrefixMaximum counts_2 s best )) ,
  TT && emp 
|--
  “ (CountPrefixMaximum counts_2 (s + 1 ) best ) ”
  &&  emp
).

Definition solver_entail_wit_7_2_split_goal_1 := 
forall (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (best: Z) (counts_2: (@list Z)) (pb_spec_2: (@list Z)) (pa_spec_2: (@list Z)) (s: Z) (PreH1 : ((Znth s counts_2 0) <= best)) (PreH2 : (s < n_pre)) (PreH3 : (Pre a b )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (0 <= s)) (PreH9 : (s <= n_pre)) (PreH10 : (PositionTable a pa_spec_2 n_pre )) (PreH11 : (PositionTable b pb_spec_2 n_pre )) (PreH12 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre (n_pre + 1 ) counts_2 )) (PreH13 : (CountPrefixMaximum counts_2 s best )) ,
  (CountPrefixMaximum counts_2 (s + 1 ) best )
.

Definition solver_return_wit_1 := 
(
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (best: Z) (counts: (@list Z)) (pb_spec_2: (@list Z)) (pa_spec_2: (@list Z)) (s: Z) (PreH1 : (s >= n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (0 <= s)) (PreH8 : (s <= n_pre)) (PreH9 : (PositionTable a pa_spec_2 n_pre )) (PreH10 : (PositionTable b pb_spec_2 n_pre )) (PreH11 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre (n_pre + 1 ) counts )) (PreH12 : (CountPrefixMaximum counts s best )) ,
  (IntArray.full pa_pre (n_pre + 1 ) pa_spec_2 )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec_2 )
  **  (IntArray.full cnt_pre n_pre counts )
|--
  EX (pb_spec: (@list Z))  (pa_spec: (@list Z)) ,
  “ (Spec a b best ) ” 
  &&  “ ((Zlength (pa_spec)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pb_spec)) = (n_pre + 1 )) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth (Znth i a 0) pa_spec 0) = i) /\ ((Znth (Znth i b 0) pb_spec 0) = i))) ”
  &&  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full_shape cnt_pre n_pre )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (best: Z) (counts: (@list Z)) (pb_spec_2: (@list Z)) (pa_spec_2: (@list Z)) (s: Z) (PreH1 : (s >= n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (0 <= s)) (PreH8 : (s <= n_pre)) (PreH9 : (PositionTable a pa_spec_2 n_pre )) (PreH10 : (PositionTable b pb_spec_2 n_pre )) (PreH11 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre (n_pre + 1 ) counts )) (PreH12 : (CountPrefixMaximum counts s best )) ,
  (IntArray.full cnt_pre n_pre counts )
|--
  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth (Znth i a 0) pa_spec_2 0) = i) /\ ((Znth (Znth i b 0) pb_spec_2 0) = i))) ” 
  &&  “ ((Zlength (pb_spec_2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pa_spec_2)) = (n_pre + 1 )) ” 
  &&  “ (Spec a b best ) ”
  &&  (IntArray.full_shape cnt_pre n_pre )
).

Definition solver_return_wit_1_split_goal_1 := 
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (best: Z) (counts: (@list Z)) (pb_spec_2: (@list Z)) (pa_spec_2: (@list Z)) (s: Z) (PreH1 : (s >= n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (0 <= s)) (PreH8 : (s <= n_pre)) (PreH9 : (PositionTable a pa_spec_2 n_pre )) (PreH10 : (PositionTable b pb_spec_2 n_pre )) (PreH11 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre (n_pre + 1 ) counts )) (PreH12 : (CountPrefixMaximum counts s best )) ,
  (IntArray.full cnt_pre n_pre counts )
|--
  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth (Znth i a 0) pa_spec_2 0) = i) /\ ((Znth (Znth i b 0) pb_spec_2 0) = i))) ”
.

Definition solver_return_wit_1_split_goal_2 := 
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (best: Z) (counts: (@list Z)) (pb_spec_2: (@list Z)) (pa_spec_2: (@list Z)) (s: Z) (PreH1 : (s >= n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (0 <= s)) (PreH8 : (s <= n_pre)) (PreH9 : (PositionTable a pa_spec_2 n_pre )) (PreH10 : (PositionTable b pb_spec_2 n_pre )) (PreH11 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre (n_pre + 1 ) counts )) (PreH12 : (CountPrefixMaximum counts s best )) ,
  (IntArray.full cnt_pre n_pre counts )
|--
  “ ((Zlength (pb_spec_2)) = (n_pre + 1 )) ”
.

Definition solver_return_wit_1_split_goal_3 := 
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (best: Z) (counts: (@list Z)) (pb_spec_2: (@list Z)) (pa_spec_2: (@list Z)) (s: Z) (PreH1 : (s >= n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (0 <= s)) (PreH8 : (s <= n_pre)) (PreH9 : (PositionTable a pa_spec_2 n_pre )) (PreH10 : (PositionTable b pb_spec_2 n_pre )) (PreH11 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre (n_pre + 1 ) counts )) (PreH12 : (CountPrefixMaximum counts s best )) ,
  (IntArray.full cnt_pre n_pre counts )
|--
  “ ((Zlength (pa_spec_2)) = (n_pre + 1 )) ”
.

Definition solver_return_wit_1_split_goal_4 := 
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (best: Z) (counts: (@list Z)) (pb_spec_2: (@list Z)) (pa_spec_2: (@list Z)) (s: Z) (PreH1 : (s >= n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (0 <= s)) (PreH8 : (s <= n_pre)) (PreH9 : (PositionTable a pa_spec_2 n_pre )) (PreH10 : (PositionTable b pb_spec_2 n_pre )) (PreH11 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre (n_pre + 1 ) counts )) (PreH12 : (CountPrefixMaximum counts s best )) ,
  (IntArray.full cnt_pre n_pre counts )
|--
  “ (Spec a b best ) ”
.

Definition solver_return_wit_1_split_goal_spatial := 
forall (cnt_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (best: Z) (counts: (@list Z)) (pb_spec_2: (@list Z)) (pa_spec_2: (@list Z)) (s: Z) (PreH1 : (s >= n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (0 <= s)) (PreH8 : (s <= n_pre)) (PreH9 : (PositionTable a pa_spec_2 n_pre )) (PreH10 : (PositionTable b pb_spec_2 n_pre )) (PreH11 : (RotationTallyPrefix pa_spec_2 pb_spec_2 n_pre (n_pre + 1 ) counts )) (PreH12 : (CountPrefixMaximum counts s best )) ,
  (IntArray.full cnt_pre n_pre counts )
|--
  (IntArray.full_shape cnt_pre n_pre )
.

Definition solver_partial_solve_wit_1_pure := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec: (@list Z)) (pb_spec: (@list Z)) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= n_pre)))) (PreH5 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 b 0)) /\ ((Znth i_2 b 0) <= n_pre)))) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (aligned_4 cnt_pre )) (PreH9 : ((Zlength (pa_spec)) = (n_pre + 1 ))) (PreH10 : ((Zlength (pb_spec)) = (n_pre + 1 ))) (PreH11 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> (((Znth (Znth i_3 a 0) pa_spec 0) = i_3) /\ ((Znth (Znth i_3 b 0) pb_spec 0) = i_3)))) ,
  ((( &( "pa" ) )) # Ptr  |-> pa_pre)
  **  ((( &( "pb" ) )) # Ptr  |-> pb_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt_pre)
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (UCharArray.undef_full cnt_pre (sizeof(INT) * n_pre ) )
|--
  “ (0 <= (sizeof(INT) * n_pre )) ” 
  &&  “ (0 = 0) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec: (@list Z)) (pb_spec: (@list Z)) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= n_pre)))) (PreH5 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 b 0)) /\ ((Znth i_2 b 0) <= n_pre)))) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (aligned_4 cnt_pre )) (PreH9 : ((Zlength (pa_spec)) = (n_pre + 1 ))) (PreH10 : ((Zlength (pb_spec)) = (n_pre + 1 ))) (PreH11 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> (((Znth (Znth i_3 a 0) pa_spec 0) = i_3) /\ ((Znth (Znth i_3 b 0) pb_spec 0) = i_3)))) ,
  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (UCharArray.undef_full cnt_pre (sizeof(INT) * n_pre ) )
|--
  “ (0 <= (sizeof(INT) * n_pre )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (Pre a b ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i a 0)) /\ ((Znth i a 0) <= n_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 b 0)) /\ ((Znth i_2 b 0) <= n_pre))) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ ((Zlength (b)) = n_pre) ” 
  &&  “ (aligned_4 cnt_pre ) ” 
  &&  “ ((Zlength (pa_spec)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pb_spec)) = (n_pre + 1 )) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> (((Znth (Znth i_3 a 0) pa_spec 0) = i_3) /\ ((Znth (Znth i_3 b 0) pb_spec 0) = i_3))) ”
  &&  (UCharArray.undef_full cnt_pre (sizeof(INT) * n_pre ) )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (1 <= v)) (PreH8 : (v <= (n_pre + 1 ))) (PreH9 : (PositionTable a pa_spec n_pre )) (PreH10 : (PositionTable b pb_spec n_pre )) (PreH11 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts )) ,
  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full cnt_pre n_pre counts )
|--
  “ (v <= n_pre) ” 
  &&  “ (Pre a b ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ ((Zlength (b)) = n_pre) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= (n_pre + 1 )) ” 
  &&  “ (PositionTable a pa_spec n_pre ) ” 
  &&  “ (PositionTable b pb_spec n_pre ) ” 
  &&  “ (RotationTallyPrefix pa_spec pb_spec n_pre v counts ) ”
  &&  (((pa_pre + (v * sizeof(INT)))) # Int  |-> (Znth v pa_spec 0))
  **  (IntArray.missing_i pa_pre v 0 (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full cnt_pre n_pre counts )
.

Definition solver_partial_solve_wit_3 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (counts: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (1 <= v)) (PreH8 : (v <= (n_pre + 1 ))) (PreH9 : (PositionTable a pa_spec n_pre )) (PreH10 : (PositionTable b pb_spec n_pre )) (PreH11 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts )) ,
  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full cnt_pre n_pre counts )
|--
  “ (v <= n_pre) ” 
  &&  “ (Pre a b ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ ((Zlength (b)) = n_pre) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= (n_pre + 1 )) ” 
  &&  “ (PositionTable a pa_spec n_pre ) ” 
  &&  “ (PositionTable b pb_spec n_pre ) ” 
  &&  “ (RotationTallyPrefix pa_spec pb_spec n_pre v counts ) ”
  &&  (((pb_pre + (v * sizeof(INT)))) # Int  |-> (Znth v pb_spec 0))
  **  (IntArray.missing_i pb_pre v 0 (n_pre + 1 ) pb_spec )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full cnt_pre n_pre counts )
.

Definition solver_partial_solve_wit_4 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec: (@list Z)) (pb_spec: (@list Z)) (counts: (@list Z)) (v: Z) (shift: Z) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : ((Zlength (b)) = n_pre)) (PreH6 : (1 <= v)) (PreH7 : (v <= n_pre)) (PreH8 : (0 <= shift)) (PreH9 : (shift < n_pre)) (PreH10 : (shift = ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) % ( n_pre ) ))) (PreH11 : (PositionTable a pa_spec n_pre )) (PreH12 : (PositionTable b pb_spec n_pre )) (PreH13 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts )) ,
  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full cnt_pre n_pre counts )
|--
  “ (Pre a b ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ ((Zlength (b)) = n_pre) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift < n_pre) ” 
  &&  “ (shift = ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) % ( n_pre ) )) ” 
  &&  “ (PositionTable a pa_spec n_pre ) ” 
  &&  “ (PositionTable b pb_spec n_pre ) ” 
  &&  “ (RotationTallyPrefix pa_spec pb_spec n_pre v counts ) ”
  &&  (((cnt_pre + (shift * sizeof(INT)))) # Int  |-> (Znth shift counts 0))
  **  (IntArray.missing_i cnt_pre shift 0 n_pre counts )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
.

Definition solver_partial_solve_wit_5 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (pa_spec: (@list Z)) (pb_spec: (@list Z)) (counts: (@list Z)) (v: Z) (shift: Z) (PreH1 : (Pre a b )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (a)))) (PreH5 : ((Zlength (b)) = n_pre)) (PreH6 : (1 <= v)) (PreH7 : (v <= n_pre)) (PreH8 : (0 <= shift)) (PreH9 : (shift < n_pre)) (PreH10 : (shift = ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) % ( n_pre ) ))) (PreH11 : (PositionTable a pa_spec n_pre )) (PreH12 : (PositionTable b pb_spec n_pre )) (PreH13 : (RotationTallyPrefix pa_spec pb_spec n_pre v counts )) ,
  (IntArray.full cnt_pre n_pre counts )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
|--
  “ (Pre a b ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ ((Zlength (b)) = n_pre) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift < n_pre) ” 
  &&  “ (shift = ((((Znth v pa_spec 0) - (Znth v pb_spec 0) ) + n_pre ) % ( n_pre ) )) ” 
  &&  “ (PositionTable a pa_spec n_pre ) ” 
  &&  “ (PositionTable b pb_spec n_pre ) ” 
  &&  “ (RotationTallyPrefix pa_spec pb_spec n_pre v counts ) ”
  &&  (((cnt_pre + (shift * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i cnt_pre shift 0 n_pre counts )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
.

Definition solver_partial_solve_wit_6 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (best: Z) (counts: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (s: Z) (PreH1 : (s < n_pre)) (PreH2 : (Pre a b )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (a)))) (PreH6 : ((Zlength (b)) = n_pre)) (PreH7 : (0 <= s)) (PreH8 : (s <= n_pre)) (PreH9 : (PositionTable a pa_spec n_pre )) (PreH10 : (PositionTable b pb_spec n_pre )) (PreH11 : (RotationTallyPrefix pa_spec pb_spec n_pre (n_pre + 1 ) counts )) (PreH12 : (CountPrefixMaximum counts s best )) ,
  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
  **  (IntArray.full cnt_pre n_pre counts )
|--
  “ (s < n_pre) ” 
  &&  “ (Pre a b ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ ((Zlength (b)) = n_pre) ” 
  &&  “ (0 <= s) ” 
  &&  “ (s <= n_pre) ” 
  &&  “ (PositionTable a pa_spec n_pre ) ” 
  &&  “ (PositionTable b pb_spec n_pre ) ” 
  &&  “ (RotationTallyPrefix pa_spec pb_spec n_pre (n_pre + 1 ) counts ) ” 
  &&  “ (CountPrefixMaximum counts s best ) ”
  &&  (((cnt_pre + (s * sizeof(INT)))) # Int  |-> (Znth s counts 0))
  **  (IntArray.missing_i cnt_pre s 0 n_pre counts )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
.

Definition solver_partial_solve_wit_7 := 
forall (cnt_pre: Z) (n_pre: Z) (pb_pre: Z) (pa_pre: Z) (b: (@list Z)) (a: (@list Z)) (best: Z) (counts: (@list Z)) (pb_spec: (@list Z)) (pa_spec: (@list Z)) (s: Z) (PreH1 : ((Znth s counts 0) > best)) (PreH2 : (s < n_pre)) (PreH3 : (Pre a b )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : ((Zlength (b)) = n_pre)) (PreH8 : (0 <= s)) (PreH9 : (s <= n_pre)) (PreH10 : (PositionTable a pa_spec n_pre )) (PreH11 : (PositionTable b pb_spec n_pre )) (PreH12 : (RotationTallyPrefix pa_spec pb_spec n_pre (n_pre + 1 ) counts )) (PreH13 : (CountPrefixMaximum counts s best )) ,
  (IntArray.full cnt_pre n_pre counts )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
|--
  “ ((Znth s counts 0) > best) ” 
  &&  “ (s < n_pre) ” 
  &&  “ (Pre a b ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ ((Zlength (b)) = n_pre) ” 
  &&  “ (0 <= s) ” 
  &&  “ (s <= n_pre) ” 
  &&  “ (PositionTable a pa_spec n_pre ) ” 
  &&  “ (PositionTable b pb_spec n_pre ) ” 
  &&  “ (RotationTallyPrefix pa_spec pb_spec n_pre (n_pre + 1 ) counts ) ” 
  &&  “ (CountPrefixMaximum counts s best ) ”
  &&  (((cnt_pre + (s * sizeof(INT)))) # Int  |-> (Znth s counts 0))
  **  (IntArray.missing_i cnt_pre s 0 n_pre counts )
  **  (IntArray.full pa_pre (n_pre + 1 ) pa_spec )
  **  (IntArray.full pb_pre (n_pre + 1 ) pb_spec )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.

End VC_Correct.
