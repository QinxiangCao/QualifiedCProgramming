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
Require Import SimpleC.EE.QCP_demos_tutorial.pos_int_pair_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_tutorial Require Import pos_int_pair_strategy_goal.
From SimpleC.EE.QCP_demos_tutorial Require Import pos_int_pair_strategy_proof.

(*----- Function diffx1 -----*)

Definition diffx1_safety_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (qy: Z) (qx: Z) (py: Z) (px: Z) (PreH1 : (qy <= INT_MAX)) (PreH2 : (py <= INT_MAX)) (PreH3 : (qx <= INT_MAX)) (PreH4 : (px <= INT_MAX)) (PreH5 : (qy >= 0)) (PreH6 : (py >= 0)) (PreH7 : (qx >= 0)) (PreH8 : (px >= 0)) ,
  (store_pos_int_pair q_pre qx qy )
  **  (store_pos_int_pair p_pre px py )
  **  ((( &( "temp" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
|--
  “ ((px - qx ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (px - qx )) ”
.

Definition diffx1_entail_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (qy: Z) (qx: Z) (py: Z) (px: Z) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  (store_pos_int_pair p_pre px py )
  **  (store_pos_int_pair q_pre qx qy )
|--
  “ (qy <= INT_MAX) ” 
  &&  “ (py <= INT_MAX) ” 
  &&  “ (qx <= INT_MAX) ” 
  &&  “ (px <= INT_MAX) ” 
  &&  “ (qy >= 0) ” 
  &&  “ (py >= 0) ” 
  &&  “ (qx >= 0) ” 
  &&  “ (px >= 0) ”
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  (store_pos_int_pair p_pre px py )
  **  (store_pos_int_pair q_pre qx qy )
.

Definition diffx1_return_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (qy: Z) (qx: Z) (py: Z) (px: Z) (PreH1 : (qy <= INT_MAX)) (PreH2 : (py <= INT_MAX)) (PreH3 : (qx <= INT_MAX)) (PreH4 : (px <= INT_MAX)) (PreH5 : (qy >= 0)) (PreH6 : (py >= 0)) (PreH7 : (qx >= 0)) (PreH8 : (px >= 0)) ,
  (store_pos_int_pair q_pre qx qy )
  **  (store_pos_int_pair p_pre px py )
|--
  “ ((px - qx ) = (px - qx )) ”
  &&  (store_pos_int_pair p_pre px py )
  **  (store_pos_int_pair q_pre qx qy )
.

Definition diffx1_partial_solve_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (qy: Z) (qx: Z) (py: Z) (px: Z) (PreH1 : (qy <= INT_MAX)) (PreH2 : (py <= INT_MAX)) (PreH3 : (qx <= INT_MAX)) (PreH4 : (px <= INT_MAX)) (PreH5 : (qy >= 0)) (PreH6 : (py >= 0)) (PreH7 : (qx >= 0)) (PreH8 : (px >= 0)) ,
  (store_pos_int_pair p_pre px py )
  **  (store_pos_int_pair q_pre qx qy )
|--
  “ (qy <= INT_MAX) ” 
  &&  “ (py <= INT_MAX) ” 
  &&  “ (qx <= INT_MAX) ” 
  &&  “ (px <= INT_MAX) ” 
  &&  “ (qy >= 0) ” 
  &&  “ (py >= 0) ” 
  &&  “ (qx >= 0) ” 
  &&  “ (px >= 0) ”
  &&  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> px)
  **  (store_pos_int_pair_y_only p_pre px py )
  **  (store_pos_int_pair q_pre qx qy )
.

Definition diffx1_partial_solve_wit_2 := 
forall (q_pre: Z) (p_pre: Z) (qy: Z) (qx: Z) (py: Z) (px: Z) (PreH1 : (qy <= INT_MAX)) (PreH2 : (py <= INT_MAX)) (PreH3 : (qx <= INT_MAX)) (PreH4 : (px <= INT_MAX)) (PreH5 : (qy >= 0)) (PreH6 : (py >= 0)) (PreH7 : (qx >= 0)) (PreH8 : (px >= 0)) ,
  (store_pos_int_pair p_pre px py )
  **  (store_pos_int_pair q_pre qx qy )
|--
  “ (qy <= INT_MAX) ” 
  &&  “ (py <= INT_MAX) ” 
  &&  “ (qx <= INT_MAX) ” 
  &&  “ (px <= INT_MAX) ” 
  &&  “ (qy >= 0) ” 
  &&  “ (py >= 0) ” 
  &&  “ (qx >= 0) ” 
  &&  “ (px >= 0) ”
  &&  ((&((q_pre)  # "int_pair" ->ₛ "a")) # Int  |-> qx)
  **  (store_pos_int_pair_y_only q_pre qx qy )
  **  (store_pos_int_pair p_pre px py )
.

(*----- Function diffx2 -----*)

Definition diffx2_safety_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (qy: Z) (qx: Z) (py: Z) (px: Z) (PreH1 : (px >= 0)) (PreH2 : (qx >= 0)) (PreH3 : (px <= INT_MAX)) (PreH4 : (qx <= INT_MAX)) ,
  (store_pos_int_pair q_pre qx qy )
  **  (store_pos_int_pair p_pre px py )
  **  ((( &( "temp" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
|--
  “ ((px - qx ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (px - qx )) ”
.

Definition diffx2_entail_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (qy: Z) (qx: Z) (py: Z) (px: Z) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  (store_pos_int_pair p_pre px py )
  **  (store_pos_int_pair q_pre qx qy )
|--
  “ (px >= 0) ” 
  &&  “ (qx >= 0) ” 
  &&  “ (px <= INT_MAX) ” 
  &&  “ (qx <= INT_MAX) ”
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  (store_pos_int_pair p_pre px py )
  **  (store_pos_int_pair q_pre qx qy )
.

Definition diffx2_return_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (qy: Z) (qx: Z) (py: Z) (px: Z) (PreH1 : (px >= 0)) (PreH2 : (qx >= 0)) (PreH3 : (px <= INT_MAX)) (PreH4 : (qx <= INT_MAX)) ,
  (store_pos_int_pair q_pre qx qy )
  **  (store_pos_int_pair p_pre px py )
|--
  “ ((px - qx ) = (px - qx )) ”
  &&  (store_pos_int_pair p_pre px py )
  **  (store_pos_int_pair q_pre qx qy )
.

Definition diffx2_partial_solve_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (qy: Z) (qx: Z) (py: Z) (px: Z) (PreH1 : (px >= 0)) (PreH2 : (qx >= 0)) (PreH3 : (px <= INT_MAX)) (PreH4 : (qx <= INT_MAX)) ,
  (store_pos_int_pair p_pre px py )
  **  (store_pos_int_pair q_pre qx qy )
|--
  “ (px >= 0) ” 
  &&  “ (qx >= 0) ” 
  &&  “ (px <= INT_MAX) ” 
  &&  “ (qx <= INT_MAX) ”
  &&  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> px)
  **  (store_pos_int_pair_y_only p_pre px py )
  **  (store_pos_int_pair q_pre qx qy )
.

Definition diffx2_partial_solve_wit_2 := 
forall (q_pre: Z) (p_pre: Z) (qy: Z) (qx: Z) (py: Z) (px: Z) (PreH1 : (px >= 0)) (PreH2 : (qx >= 0)) (PreH3 : (px <= INT_MAX)) (PreH4 : (qx <= INT_MAX)) ,
  (store_pos_int_pair p_pre px py )
  **  (store_pos_int_pair q_pre qx qy )
|--
  “ (px >= 0) ” 
  &&  “ (qx >= 0) ” 
  &&  “ (px <= INT_MAX) ” 
  &&  “ (qx <= INT_MAX) ”
  &&  ((&((q_pre)  # "int_pair" ->ₛ "a")) # Int  |-> qx)
  **  (store_pos_int_pair_y_only q_pre qx qy )
  **  (store_pos_int_pair p_pre px py )
.

(*----- Function getx -----*)

Definition getx_return_wit_1 := 
forall (p_pre: Z) (y: Z) (x: Z) ,
  (store_pos_int_pair p_pre x y )
|--
  “ (x >= 0) ”
  &&  (store_pos_int_pair p_pre x y )
.

Definition getx_partial_solve_wit_1 := 
forall (p_pre: Z) (y: Z) (x: Z) ,
  (store_pos_int_pair p_pre x y )
|--
  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> x)
  **  (store_pos_int_pair_y_only p_pre x y )
.

(*----- Function slow_sub -----*)

Definition slow_sub_safety_wit_1 := 
forall (p_pre: Z) (y: Z) (x: Z) (y0: Z) (x0: Z) (PreH1 : (x >= y)) (PreH2 : (x0 >= 0)) (PreH3 : (y0 >= 0)) (PreH4 : ((x - x0 ) = (y - y0 ))) (PreH5 : (x >= x0)) ,
  (store_pos_int_pair p_pre x0 y0 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition slow_sub_safety_wit_2 := 
(
forall (p_pre: Z) (y: Z) (x: Z) (y0: Z) (x0: Z) (PreH1 : (y0 <> 0)) (PreH2 : (x >= y)) (PreH3 : (x0 >= 0)) (PreH4 : (y0 >= 0)) (PreH5 : ((x - x0 ) = (y - y0 ))) (PreH6 : (x >= x0)) ,
  (store_pos_int_pair p_pre x0 y0 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((x0 - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x0 - 1 )) ”
) \/
(
forall (p_pre: Z) (y: Z) (x: Z) (y0: Z) (x0: Z) (PreH1 : (y0 <> 0)) (PreH2 : (x >= y)) (PreH3 : (x0 >= 0)) (PreH4 : (y0 >= 0)) (PreH5 : ((x - x0 ) = (y - y0 ))) (PreH6 : (x >= x0)) ,
  (store_pos_int_pair p_pre x0 y0 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((x0 - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x0 - 1 )) ”
).

Definition slow_sub_safety_wit_2_split_goal_1 := 
forall (p_pre: Z) (y: Z) (x: Z) (y0: Z) (x0: Z) (PreH1 : (y0 <> 0)) (PreH2 : (x >= y)) (PreH3 : (x0 >= 0)) (PreH4 : (y0 >= 0)) (PreH5 : ((x - x0 ) = (y - y0 ))) (PreH6 : (x >= x0)) ,
  (store_pos_int_pair p_pre x0 y0 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((x0 - 1 ) <= INT_MAX) ”
.

Definition slow_sub_safety_wit_2_split_goal_2 := 
forall (p_pre: Z) (y: Z) (x: Z) (y0: Z) (x0: Z) (PreH1 : (y0 <> 0)) (PreH2 : (x >= y)) (PreH3 : (x0 >= 0)) (PreH4 : (y0 >= 0)) (PreH5 : ((x - x0 ) = (y - y0 ))) (PreH6 : (x >= x0)) ,
  (store_pos_int_pair p_pre x0 y0 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((INT_MIN) <= (x0 - 1 )) ”
.

Definition slow_sub_safety_wit_3 := 
(
forall (p_pre: Z) (y: Z) (x: Z) (y0: Z) (x0: Z) (PreH1 : (y0 <> 0)) (PreH2 : (x >= y)) (PreH3 : (x0 >= 0)) (PreH4 : (y0 >= 0)) (PreH5 : ((x - x0 ) = (y - y0 ))) (PreH6 : (x >= x0)) ,
  (store_pos_int_pair p_pre (x0 - 1 ) y0 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((y0 - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y0 - 1 )) ”
) \/
(
forall (p_pre: Z) (y: Z) (x: Z) (y0: Z) (x0: Z) (PreH1 : (y0 <> 0)) (PreH2 : (x >= y)) (PreH3 : (x0 >= 0)) (PreH4 : (y0 >= 0)) (PreH5 : ((x - x0 ) = (y - y0 ))) (PreH6 : (x >= x0)) ,
  (store_pos_int_pair p_pre (x0 - 1 ) y0 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((y0 - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y0 - 1 )) ”
).

Definition slow_sub_safety_wit_3_split_goal_1 := 
forall (p_pre: Z) (y: Z) (x: Z) (y0: Z) (x0: Z) (PreH1 : (y0 <> 0)) (PreH2 : (x >= y)) (PreH3 : (x0 >= 0)) (PreH4 : (y0 >= 0)) (PreH5 : ((x - x0 ) = (y - y0 ))) (PreH6 : (x >= x0)) ,
  (store_pos_int_pair p_pre (x0 - 1 ) y0 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((y0 - 1 ) <= INT_MAX) ”
.

Definition slow_sub_safety_wit_3_split_goal_2 := 
forall (p_pre: Z) (y: Z) (x: Z) (y0: Z) (x0: Z) (PreH1 : (y0 <> 0)) (PreH2 : (x >= y)) (PreH3 : (x0 >= 0)) (PreH4 : (y0 >= 0)) (PreH5 : ((x - x0 ) = (y - y0 ))) (PreH6 : (x >= x0)) ,
  (store_pos_int_pair p_pre (x0 - 1 ) y0 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((INT_MIN) <= (y0 - 1 )) ”
.

Definition slow_sub_entail_wit_1 := 
forall (p_pre: Z) (y: Z) (x: Z) (PreH1 : (x >= y)) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_pos_int_pair p_pre x y )
|--
  EX (y0: Z)  (x0: Z) ,
  “ (x >= y) ” 
  &&  “ (x0 >= 0) ” 
  &&  “ (y0 >= 0) ” 
  &&  “ ((x - x0 ) = (y - y0 )) ” 
  &&  “ (x >= x0) ”
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_pos_int_pair p_pre x0 y0 )
.

Definition slow_sub_entail_wit_2 := 
forall (p_pre: Z) (y: Z) (x: Z) (y0_2: Z) (x0_2: Z) (PreH1 : (y0_2 <> 0)) (PreH2 : (x >= y)) (PreH3 : (x0_2 >= 0)) (PreH4 : (y0_2 >= 0)) (PreH5 : ((x - x0_2 ) = (y - y0_2 ))) (PreH6 : (x >= x0_2)) ,
  (store_pos_int_pair p_pre (x0_2 - 1 ) (y0_2 - 1 ) )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  EX (y0: Z)  (x0: Z) ,
  “ (x >= y) ” 
  &&  “ (x0 >= 0) ” 
  &&  “ (y0 >= 0) ” 
  &&  “ ((x - x0 ) = (y - y0 )) ” 
  &&  “ (x >= x0) ”
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_pos_int_pair p_pre x0 y0 )
.

Definition slow_sub_return_wit_1 := 
(
forall (p_pre: Z) (y: Z) (x: Z) (y0: Z) (x0: Z) (PreH1 : (y0 = 0)) (PreH2 : (x >= y)) (PreH3 : (x0 >= 0)) (PreH4 : (y0 >= 0)) (PreH5 : ((x - x0 ) = (y - y0 ))) (PreH6 : (x >= x0)) ,
  (store_pos_int_pair p_pre x0 y0 )
|--
  (store_pos_int_pair p_pre (x - y ) 0 )
) \/
(
forall (p_pre: Z) (y: Z) (x: Z) (y0: Z) (x0: Z) (PreH1 : (y0 = 0)) (PreH2 : (x >= y)) (PreH3 : (x0 >= 0)) (PreH4 : (y0 >= 0)) (PreH5 : ((x - x0 ) = (y - y0 ))) (PreH6 : (x >= x0)) ,
  (store_pos_int_pair p_pre x0 y0 )
|--
  (store_pos_int_pair p_pre (x - y ) 0 )
).

Definition slow_sub_return_wit_1_split_goal_spatial := 
forall (p_pre: Z) (y: Z) (x: Z) (y0: Z) (x0: Z) (PreH1 : (y0 = 0)) (PreH2 : (x >= y)) (PreH3 : (x0 >= 0)) (PreH4 : (y0 >= 0)) (PreH5 : ((x - x0 ) = (y - y0 ))) (PreH6 : (x >= x0)) ,
  (store_pos_int_pair p_pre x0 y0 )
|--
  (store_pos_int_pair p_pre (x - y ) 0 )
.

Definition slow_sub_partial_solve_wit_1 := 
forall (p_pre: Z) (y: Z) (x: Z) (y0: Z) (x0: Z) (PreH1 : (x >= y)) (PreH2 : (x0 >= 0)) (PreH3 : (y0 >= 0)) (PreH4 : ((x - x0 ) = (y - y0 ))) (PreH5 : (x >= x0)) ,
  (store_pos_int_pair p_pre x0 y0 )
|--
  “ (x >= y) ” 
  &&  “ (x0 >= 0) ” 
  &&  “ (y0 >= 0) ” 
  &&  “ ((x - x0 ) = (y - y0 )) ” 
  &&  “ (x >= x0) ”
  &&  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> y0)
  **  (store_pos_int_pair_x_only p_pre x0 y0 )
.

Definition slow_sub_partial_solve_wit_2 := 
forall (p_pre: Z) (y: Z) (x: Z) (y0: Z) (x0: Z) (PreH1 : (y0 <> 0)) (PreH2 : (x >= y)) (PreH3 : (x0 >= 0)) (PreH4 : (y0 >= 0)) (PreH5 : ((x - x0 ) = (y - y0 ))) (PreH6 : (x >= x0)) ,
  (store_pos_int_pair p_pre x0 y0 )
|--
  “ (y0 <> 0) ” 
  &&  “ (x >= y) ” 
  &&  “ (x0 >= 0) ” 
  &&  “ (y0 >= 0) ” 
  &&  “ ((x - x0 ) = (y - y0 )) ” 
  &&  “ (x >= x0) ”
  &&  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> x0)
  **  (store_pos_int_pair_y_only p_pre x0 y0 )
.

Definition slow_sub_partial_solve_wit_3 := 
forall (p_pre: Z) (y: Z) (x: Z) (y0: Z) (x0: Z) (PreH1 : (y0 <> 0)) (PreH2 : (x >= y)) (PreH3 : (x0 >= 0)) (PreH4 : (y0 >= 0)) (PreH5 : ((x - x0 ) = (y - y0 ))) (PreH6 : (x >= x0)) ,
  (store_pos_int_pair p_pre x0 y0 )
|--
  “ (y0 <> 0) ” 
  &&  “ (x >= y) ” 
  &&  “ (x0 >= 0) ” 
  &&  “ (y0 >= 0) ” 
  &&  “ ((x - x0 ) = (y - y0 )) ” 
  &&  “ (x >= x0) ”
  &&  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |->_)
  **  (store_pos_int_pair_y_only p_pre x0 y0 )
.

Definition slow_sub_partial_solve_wit_4 := 
forall (p_pre: Z) (y: Z) (x: Z) (y0: Z) (x0: Z) (PreH1 : (y0 <> 0)) (PreH2 : (x >= y)) (PreH3 : (x0 >= 0)) (PreH4 : (y0 >= 0)) (PreH5 : ((x - x0 ) = (y - y0 ))) (PreH6 : (x >= x0)) ,
  (store_pos_int_pair p_pre (x0 - 1 ) y0 )
|--
  “ (y0 <> 0) ” 
  &&  “ (x >= y) ” 
  &&  “ (x0 >= 0) ” 
  &&  “ (y0 >= 0) ” 
  &&  “ ((x - x0 ) = (y - y0 )) ” 
  &&  “ (x >= x0) ”
  &&  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> y0)
  **  (store_pos_int_pair_x_only p_pre (x0 - 1 ) y0 )
.

Definition slow_sub_partial_solve_wit_5 := 
forall (p_pre: Z) (y: Z) (x: Z) (y0: Z) (x0: Z) (PreH1 : (y0 <> 0)) (PreH2 : (x >= y)) (PreH3 : (x0 >= 0)) (PreH4 : (y0 >= 0)) (PreH5 : ((x - x0 ) = (y - y0 ))) (PreH6 : (x >= x0)) ,
  (store_pos_int_pair p_pre (x0 - 1 ) y0 )
|--
  “ (y0 <> 0) ” 
  &&  “ (x >= y) ” 
  &&  “ (x0 >= 0) ” 
  &&  “ (y0 >= 0) ” 
  &&  “ ((x - x0 ) = (y - y0 )) ” 
  &&  “ (x >= x0) ”
  &&  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |->_)
  **  (store_pos_int_pair_x_only p_pre (x0 - 1 ) y0 )
.

(*----- Function swap -----*)

Definition swap_entail_wit_1 := 
forall (p_pre: Z) (y: Z) (x: Z) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_pos_int_pair p_pre x y )
|--
  “ (y >= 0) ” 
  &&  “ (x >= 0) ”
  &&  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> y)
  **  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> x)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
.

Definition swap_entail_wit_2 := 
forall (p_pre: Z) (y: Z) (x: Z) (PreH1 : (y >= 0)) (PreH2 : (x >= 0)) ,
  ((( &( "temp" ) )) # Int  |-> x)
  **  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> x)
  **  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> y)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (y >= 0) ” 
  &&  “ (x >= 0) ”
  &&  (store_pos_int_pair p_pre y x )
  **  ((( &( "temp" ) )) # Int  |-> x)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
.

Definition swap_return_wit_1 := 
forall (p_pre: Z) (y: Z) (x: Z) (PreH1 : (y >= 0)) (PreH2 : (x >= 0)) ,
  (store_pos_int_pair p_pre y x )
|--
  (store_pos_int_pair p_pre y x )
.

(*----- Function swap2 -----*)

Definition swap2_entail_wit_1 := 
forall (p_pre: Z) (y: Z) (x: Z) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_pos_int_pair p_pre x y )
|--
  “ (x >= 0) ” 
  &&  “ (y >= 0) ”
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_pos_int_pair p_pre x y )
.

Definition swap2_return_wit_1 := 
forall (p_pre: Z) (y: Z) (x: Z) (PreH1 : (x >= 0)) (PreH2 : (y >= 0)) ,
  (store_pos_int_pair p_pre y x )
|--
  (store_pos_int_pair p_pre y x )
.

Definition swap2_partial_solve_wit_1 := 
forall (p_pre: Z) (y: Z) (x: Z) (PreH1 : (x >= 0)) (PreH2 : (y >= 0)) ,
  (store_pos_int_pair p_pre x y )
|--
  “ (x >= 0) ” 
  &&  “ (y >= 0) ”
  &&  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |-> x)
  **  (store_pos_int_pair_y_only p_pre x y )
.

Definition swap2_partial_solve_wit_2 := 
forall (p_pre: Z) (y: Z) (x: Z) (PreH1 : (x >= 0)) (PreH2 : (y >= 0)) ,
  (store_pos_int_pair p_pre x y )
|--
  “ (x >= 0) ” 
  &&  “ (y >= 0) ”
  &&  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |-> y)
  **  (store_pos_int_pair_x_only p_pre x y )
.

Definition swap2_partial_solve_wit_3 := 
forall (p_pre: Z) (y: Z) (x: Z) (PreH1 : (x >= 0)) (PreH2 : (y >= 0)) ,
  (store_pos_int_pair p_pre x y )
|--
  “ (x >= 0) ” 
  &&  “ (y >= 0) ”
  &&  ((&((p_pre)  # "int_pair" ->ₛ "a")) # Int  |->_)
  **  (store_pos_int_pair_y_only p_pre x y )
.

Definition swap2_partial_solve_wit_4 := 
forall (p_pre: Z) (y: Z) (x: Z) (PreH1 : (x >= 0)) (PreH2 : (y >= 0)) ,
  (store_pos_int_pair p_pre y y )
|--
  “ (x >= 0) ” 
  &&  “ (y >= 0) ”
  &&  ((&((p_pre)  # "int_pair" ->ₛ "b")) # Int  |->_)
  **  (store_pos_int_pair_x_only p_pre y y )
.

Module Type VC_Correct.

Include pos_int_pair_Strategy_Correct.

Axiom proof_of_diffx1_safety_wit_1 : diffx1_safety_wit_1.
Axiom proof_of_diffx1_entail_wit_1 : diffx1_entail_wit_1.
Axiom proof_of_diffx1_return_wit_1 : diffx1_return_wit_1.
Axiom proof_of_diffx1_partial_solve_wit_1 : diffx1_partial_solve_wit_1.
Axiom proof_of_diffx1_partial_solve_wit_2 : diffx1_partial_solve_wit_2.
Axiom proof_of_diffx2_safety_wit_1 : diffx2_safety_wit_1.
Axiom proof_of_diffx2_entail_wit_1 : diffx2_entail_wit_1.
Axiom proof_of_diffx2_return_wit_1 : diffx2_return_wit_1.
Axiom proof_of_diffx2_partial_solve_wit_1 : diffx2_partial_solve_wit_1.
Axiom proof_of_diffx2_partial_solve_wit_2 : diffx2_partial_solve_wit_2.
Axiom proof_of_getx_return_wit_1 : getx_return_wit_1.
Axiom proof_of_getx_partial_solve_wit_1 : getx_partial_solve_wit_1.
Axiom proof_of_slow_sub_safety_wit_1 : slow_sub_safety_wit_1.
Axiom proof_of_slow_sub_safety_wit_2 : slow_sub_safety_wit_2.
Axiom proof_of_slow_sub_safety_wit_3 : slow_sub_safety_wit_3.
Axiom proof_of_slow_sub_entail_wit_1 : slow_sub_entail_wit_1.
Axiom proof_of_slow_sub_entail_wit_2 : slow_sub_entail_wit_2.
Axiom proof_of_slow_sub_return_wit_1 : slow_sub_return_wit_1.
Axiom proof_of_slow_sub_partial_solve_wit_1 : slow_sub_partial_solve_wit_1.
Axiom proof_of_slow_sub_partial_solve_wit_2 : slow_sub_partial_solve_wit_2.
Axiom proof_of_slow_sub_partial_solve_wit_3 : slow_sub_partial_solve_wit_3.
Axiom proof_of_slow_sub_partial_solve_wit_4 : slow_sub_partial_solve_wit_4.
Axiom proof_of_slow_sub_partial_solve_wit_5 : slow_sub_partial_solve_wit_5.
Axiom proof_of_swap_entail_wit_1 : swap_entail_wit_1.
Axiom proof_of_swap_entail_wit_2 : swap_entail_wit_2.
Axiom proof_of_swap_return_wit_1 : swap_return_wit_1.
Axiom proof_of_swap2_entail_wit_1 : swap2_entail_wit_1.
Axiom proof_of_swap2_return_wit_1 : swap2_return_wit_1.
Axiom proof_of_swap2_partial_solve_wit_1 : swap2_partial_solve_wit_1.
Axiom proof_of_swap2_partial_solve_wit_2 : swap2_partial_solve_wit_2.
Axiom proof_of_swap2_partial_solve_wit_3 : swap2_partial_solve_wit_3.
Axiom proof_of_swap2_partial_solve_wit_4 : swap2_partial_solve_wit_4.

End VC_Correct.
