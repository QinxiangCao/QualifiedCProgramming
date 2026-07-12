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
Require Import SimpleC.EE.QCP_demos_human.eval_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_human Require Import eval_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import eval_strategy_proof.

(*----- Function eval -----*)

Definition eval_safety_wit_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (PreH1 : (safe_eval e0 l )) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eval_safety_wit_2 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (PreH1 : (safe_eval e0 l )) (PreH2 : (0 <> e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_safety_wit_3 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (PreH1 : (safe_eval e0 l )) (PreH2 : (0 <> e_t)) (PreH3 : (1 <> e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition eval_safety_wit_4 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (PreH1 : (2 = 2)) (PreH2 : (e0 = (EBinop (op) (e1) (e2)))) (PreH3 : (v_3 = (BinOpID (op)))) (PreH4 : (safe_eval e0 l )) (PreH5 : (0 <> e_t)) (PreH6 : (1 <> e_t)) (PreH7 : (2 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (11 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 11) ”
.

Definition eval_safety_wit_5 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 = 11)) (PreH4 : (e0 = (EBinop (op) (e1) (e2)))) (PreH5 : (v_3 = (BinOpID (op)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 <> e_t)) (PreH8 : (1 <> e_t)) (PreH9 : (2 = e_t)) (PreH10 : (retval <> 0)) (PreH11 : (retval_2 <> 0)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_safety_wit_6 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 = 11)) (PreH4 : (e0 = (EBinop (op) (e1) (e2)))) (PreH5 : (v_3 = (BinOpID (op)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 <> e_t)) (PreH8 : (1 <> e_t)) (PreH9 : (2 = e_t)) (PreH10 : (retval <> 0)) (PreH11 : (retval_2 = 0)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eval_safety_wit_7 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (retval = (expr_eval (e1) (l)))) (PreH2 : (v_3 = 11)) (PreH3 : (e0 = (EBinop (op) (e1) (e2)))) (PreH4 : (v_3 = (BinOpID (op)))) (PreH5 : (safe_eval e0 l )) (PreH6 : (0 <> e_t)) (PreH7 : (1 <> e_t)) (PreH8 : (2 = e_t)) (PreH9 : (retval = 0)) ,
  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eval_safety_wit_8 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (PreH1 : (v_3 <> 11)) (PreH2 : (2 = 2)) (PreH3 : (e0 = (EBinop (op) (e1) (e2)))) (PreH4 : (v_3 = (BinOpID (op)))) (PreH5 : (safe_eval e0 l )) (PreH6 : (0 <> e_t)) (PreH7 : (1 <> e_t)) (PreH8 : (2 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (12 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 12) ”
.

Definition eval_safety_wit_9 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (retval = (expr_eval (e1) (l)))) (PreH2 : (v_3 = 12)) (PreH3 : (v_3 <> 11)) (PreH4 : (e0 = (EBinop (op) (e1) (e2)))) (PreH5 : (v_3 = (BinOpID (op)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 <> e_t)) (PreH8 : (1 <> e_t)) (PreH9 : (2 = e_t)) (PreH10 : (retval <> 0)) ,
  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_safety_wit_10 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 = 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (retval = 0)) (PreH12 : (retval_2 <> 0)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_safety_wit_11 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 = 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (retval = 0)) (PreH12 : (retval_2 = 0)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eval_safety_wit_12 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eval_safety_wit_13 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + retval_2 )) ”
) \/
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + retval_2 )) ”
).

Definition eval_safety_wit_13_split_goal_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ ((retval + retval_2 ) <= INT_MAX) ”
.

Definition eval_safety_wit_13_split_goal_2 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ ((INT_MIN) <= (retval + retval_2 )) ”
.

Definition eval_safety_wit_14 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_safety_wit_15 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ ((retval - retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - retval_2 )) ”
) \/
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ ((retval - retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - retval_2 )) ”
).

Definition eval_safety_wit_15_split_goal_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ ((retval - retval_2 ) <= INT_MAX) ”
.

Definition eval_safety_wit_15_split_goal_2 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ ((INT_MIN) <= (retval - retval_2 )) ”
.

Definition eval_safety_wit_16 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition eval_safety_wit_17 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ ((retval * retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval * retval_2 )) ”
) \/
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ ((retval * retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval * retval_2 )) ”
).

Definition eval_safety_wit_17_split_goal_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ ((retval * retval_2 ) <= INT_MAX) ”
.

Definition eval_safety_wit_17_split_goal_2 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ ((INT_MIN) <= (retval * retval_2 )) ”
.

Definition eval_safety_wit_18 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition eval_safety_wit_19 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ ((retval <> (INT_MIN)) \/ (retval_2 <> (-1))) ” 
  &&  “ (retval_2 <> 0) ”
) \/
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ ((retval <> (INT_MIN)) \/ (retval_2 <> (-1))) ” 
  &&  “ (retval_2 <> 0) ”
).

Definition eval_safety_wit_19_split_goal_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ ((retval <> (INT_MIN)) \/ (retval_2 <> (-1))) ”
.

Definition eval_safety_wit_19_split_goal_2 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (retval_2 <> 0) ”
.

Definition eval_safety_wit_20 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 <> v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition eval_safety_wit_21 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 <> v_3)) (PreH15 : (4 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ ((retval <> (INT_MIN)) \/ (retval_2 <> (-1))) ” 
  &&  “ (retval_2 <> 0) ”
) \/
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 <> v_3)) (PreH15 : (4 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ ((retval <> (INT_MIN)) \/ (retval_2 <> (-1))) ” 
  &&  “ (retval_2 <> 0) ”
).

Definition eval_safety_wit_21_split_goal_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 <> v_3)) (PreH15 : (4 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ ((retval <> (INT_MIN)) \/ (retval_2 <> (-1))) ”
.

Definition eval_safety_wit_21_split_goal_2 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 <> v_3)) (PreH15 : (4 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (retval_2 <> 0) ”
.

Definition eval_safety_wit_22 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 <> v_3)) (PreH15 : (4 <> v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition eval_safety_wit_23 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 <> v_3)) (PreH15 : (4 <> v_3)) (PreH16 : (5 <> v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (6 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 6) ”
.

Definition eval_safety_wit_24 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 <> v_3)) (PreH15 : (4 <> v_3)) (PreH16 : (5 <> v_3)) (PreH17 : (6 <> v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (7 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 7) ”
.

Definition eval_safety_wit_25 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 <> v_3)) (PreH15 : (4 <> v_3)) (PreH16 : (5 <> v_3)) (PreH17 : (6 <> v_3)) (PreH18 : (7 <> v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition eval_safety_wit_26 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 <> v_3)) (PreH15 : (4 <> v_3)) (PreH16 : (5 <> v_3)) (PreH17 : (6 <> v_3)) (PreH18 : (7 <> v_3)) (PreH19 : (8 <> v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (9 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 9) ”
.

Definition eval_safety_wit_27 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 <> v_3)) (PreH15 : (4 <> v_3)) (PreH16 : (5 <> v_3)) (PreH17 : (6 <> v_3)) (PreH18 : (7 <> v_3)) (PreH19 : (8 <> v_3)) (PreH20 : (9 <> v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition eval_safety_wit_28 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 <> v_3)) (PreH15 : (4 <> v_3)) (PreH16 : (5 <> v_3)) (PreH17 : (6 <> v_3)) (PreH18 : (7 <> v_3)) (PreH19 : (8 <> v_3)) (PreH20 : (9 <> v_3)) (PreH21 : (10 <> v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ False ”
) \/
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 <> v_3)) (PreH15 : (4 <> v_3)) (PreH16 : (5 <> v_3)) (PreH17 : (6 <> v_3)) (PreH18 : (7 <> v_3)) (PreH19 : (8 <> v_3)) (PreH20 : (9 <> v_3)) (PreH21 : (10 <> v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ False ”
).

Definition eval_safety_wit_28_split_goal_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 <> v_3)) (PreH15 : (4 <> v_3)) (PreH16 : (5 <> v_3)) (PreH17 : (6 <> v_3)) (PreH18 : (7 <> v_3)) (PreH19 : (8 <> v_3)) (PreH20 : (9 <> v_3)) (PreH21 : (10 <> v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ False ”
.

Definition eval_safety_wit_29 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (PreH1 : (safe_eval e0 l )) (PreH2 : (0 <> e_t)) (PreH3 : (1 <> e_t)) (PreH4 : (2 <> e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition eval_safety_wit_30 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (PreH1 : (3 = 3)) (PreH2 : (e0 = (EUnop (op) (e1)))) (PreH3 : (v_2 = (UnOpID (op)))) (PreH4 : (safe_eval e0 l )) (PreH5 : (0 <> e_t)) (PreH6 : (1 <> e_t)) (PreH7 : (2 <> e_t)) (PreH8 : (3 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  (store_expr v e1 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_safety_wit_31 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) (PreH1 : (retval = (expr_eval (e1) (l)))) (PreH2 : (v_2 <> 1)) (PreH3 : (e0 = (EUnop (op) (e1)))) (PreH4 : (v_2 = (UnOpID (op)))) (PreH5 : (safe_eval e0 l )) (PreH6 : (0 <> e_t)) (PreH7 : (1 <> e_t)) (PreH8 : (2 <> e_t)) (PreH9 : (3 = e_t)) ,
  (store_expr v e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (retval <> (INT_MIN)) ”
) \/
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) (PreH1 : (retval = (expr_eval (e1) (l)))) (PreH2 : (v_2 <> 1)) (PreH3 : (e0 = (EUnop (op) (e1)))) (PreH4 : (v_2 = (UnOpID (op)))) (PreH5 : (safe_eval e0 l )) (PreH6 : (0 <> e_t)) (PreH7 : (1 <> e_t)) (PreH8 : (2 <> e_t)) (PreH9 : (3 = e_t)) ,
  (store_expr v e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (retval <> (INT_MIN)) ”
).

Definition eval_safety_wit_31_split_goal_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) (PreH1 : (retval = (expr_eval (e1) (l)))) (PreH2 : (v_2 <> 1)) (PreH3 : (e0 = (EUnop (op) (e1)))) (PreH4 : (v_2 = (UnOpID (op)))) (PreH5 : (safe_eval e0 l )) (PreH6 : (0 <> e_t)) (PreH7 : (1 <> e_t)) (PreH8 : (2 <> e_t)) (PreH9 : (3 = e_t)) ,
  (store_expr v e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (retval <> (INT_MIN)) ”
.

Definition eval_safety_wit_32 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (PreH1 : (safe_eval e0 l )) (PreH2 : (0 <> e_t)) (PreH3 : (1 <> e_t)) (PreH4 : (2 <> e_t)) (PreH5 : (3 <> e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ False ”
) \/
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (PreH1 : (safe_eval e0 l )) (PreH2 : (0 <> e_t)) (PreH3 : (1 <> e_t)) (PreH4 : (2 <> e_t)) (PreH5 : (3 <> e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ False ”
).

Definition eval_safety_wit_32_split_goal_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (PreH1 : (safe_eval e0 l )) (PreH2 : (0 <> e_t)) (PreH3 : (1 <> e_t)) (PreH4 : (2 <> e_t)) (PreH5 : (3 <> e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ False ”
.

Definition eval_return_wit_1 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) (PreH1 : (retval = (expr_eval (e1) (l)))) (PreH2 : (v_2 <> 1)) (PreH3 : (e0 = (EUnop (op) (e1)))) (PreH4 : (v_2 = (UnOpID (op)))) (PreH5 : (safe_eval e0 l )) (PreH6 : (0 <> e_t)) (PreH7 : (1 <> e_t)) (PreH8 : (2 <> e_t)) (PreH9 : (3 = e_t)) ,
  (store_expr v e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
|--
  “ ((-retval) = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (v_2 >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : (retval = (expr_eval (e1) (l)))) (PreH6 : (v_2 <> 1)) (PreH7 : (e0 = (EUnop (op) (e1)))) (PreH8 : (v_2 = (UnOpID (op)))) (PreH9 : (safe_eval e0 l )) (PreH10 : (0 <> e_t)) (PreH11 : (1 <> e_t)) (PreH12 : (2 <> e_t)) (PreH13 : (3 = e_t)) ,
  (store_expr v e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
|--
  “ ((-retval) = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_1_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (v_2 >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : (retval = (expr_eval (e1) (l)))) (PreH6 : (v_2 <> 1)) (PreH7 : (e0 = (EUnop (op) (e1)))) (PreH8 : (v_2 = (UnOpID (op)))) (PreH9 : (safe_eval e0 l )) (PreH10 : (0 <> e_t)) (PreH11 : (1 <> e_t)) (PreH12 : (2 <> e_t)) (PreH13 : (3 = e_t)) ,
  (store_expr v e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
|--
  “ ((-retval) = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_1_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (v_2 >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : (retval = (expr_eval (e1) (l)))) (PreH6 : (v_2 <> 1)) (PreH7 : (e0 = (EUnop (op) (e1)))) (PreH8 : (v_2 = (UnOpID (op)))) (PreH9 : (safe_eval e0 l )) (PreH10 : (0 <> e_t)) (PreH11 : (1 <> e_t)) (PreH12 : (2 <> e_t)) (PreH13 : (3 = e_t)) ,
  (store_expr v e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_2 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_2 = 1)) (PreH4 : (e0 = (EUnop (op) (e1)))) (PreH5 : (v_2 = (UnOpID (op)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 <> e_t)) (PreH8 : (1 <> e_t)) (PreH9 : (2 <> e_t)) (PreH10 : (3 = e_t)) ,
  (store_expr v e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (v_2 >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_2 = 1)) (PreH8 : (e0 = (EUnop (op) (e1)))) (PreH9 : (v_2 = (UnOpID (op)))) (PreH10 : (safe_eval e0 l )) (PreH11 : (0 <> e_t)) (PreH12 : (1 <> e_t)) (PreH13 : (2 <> e_t)) (PreH14 : (3 = e_t)) ,
  (store_expr v e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_2_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (v_2 >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_2 = 1)) (PreH8 : (e0 = (EUnop (op) (e1)))) (PreH9 : (v_2 = (UnOpID (op)))) (PreH10 : (safe_eval e0 l )) (PreH11 : (0 <> e_t)) (PreH12 : (1 <> e_t)) (PreH13 : (2 <> e_t)) (PreH14 : (3 = e_t)) ,
  (store_expr v e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_2_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (v_2 >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_2 = 1)) (PreH8 : (e0 = (EUnop (op) (e1)))) (PreH9 : (v_2 = (UnOpID (op)))) (PreH10 : (safe_eval e0 l )) (PreH11 : (0 <> e_t)) (PreH12 : (1 <> e_t)) (PreH13 : (2 <> e_t)) (PreH14 : (3 = e_t)) ,
  (store_expr v e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_3 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_2 = 1)) (PreH4 : (e0 = (EUnop (op) (e1)))) (PreH5 : (v_2 = (UnOpID (op)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 <> e_t)) (PreH8 : (1 <> e_t)) (PreH9 : (2 <> e_t)) (PreH10 : (3 = e_t)) ,
  (store_expr v e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (v_2 >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_2 = 1)) (PreH8 : (e0 = (EUnop (op) (e1)))) (PreH9 : (v_2 = (UnOpID (op)))) (PreH10 : (safe_eval e0 l )) (PreH11 : (0 <> e_t)) (PreH12 : (1 <> e_t)) (PreH13 : (2 <> e_t)) (PreH14 : (3 = e_t)) ,
  (store_expr v e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_3_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (v_2 >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_2 = 1)) (PreH8 : (e0 = (EUnop (op) (e1)))) (PreH9 : (v_2 = (UnOpID (op)))) (PreH10 : (safe_eval e0 l )) (PreH11 : (0 <> e_t)) (PreH12 : (1 <> e_t)) (PreH13 : (2 <> e_t)) (PreH14 : (3 = e_t)) ,
  (store_expr v e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_3_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (retval: Z) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (v_2 >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_2 = 1)) (PreH8 : (e0 = (EUnop (op) (e1)))) (PreH9 : (v_2 = (UnOpID (op)))) (PreH10 : (safe_eval e0 l )) (PreH11 : (0 <> e_t)) (PreH12 : (1 <> e_t)) (PreH13 : (2 <> e_t)) (PreH14 : (3 = e_t)) ,
  (store_expr v e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_4 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (expr_eval (e2) (l)))) (PreH3 : (retval = (expr_eval (e1) (l)))) (PreH4 : (v_3 <> 12)) (PreH5 : (v_3 <> 11)) (PreH6 : (e0 = (EBinop (op) (e1) (e2)))) (PreH7 : (v_3 = (BinOpID (op)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 <> e_t)) (PreH11 : (2 = e_t)) (PreH12 : (0 <> v_3)) (PreH13 : (1 <> v_3)) (PreH14 : (2 <> v_3)) (PreH15 : (3 <> v_3)) (PreH16 : (4 <> v_3)) (PreH17 : (5 <> v_3)) (PreH18 : (6 <> v_3)) (PreH19 : (7 <> v_3)) (PreH20 : (8 <> v_3)) (PreH21 : (9 <> v_3)) (PreH22 : (10 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 <> v_3)) (PreH24 : (8 <> v_3)) (PreH25 : (9 <> v_3)) (PreH26 : (10 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_4_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 <> v_3)) (PreH24 : (8 <> v_3)) (PreH25 : (9 <> v_3)) (PreH26 : (10 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_4_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 <> v_3)) (PreH24 : (8 <> v_3)) (PreH25 : (9 <> v_3)) (PreH26 : (10 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_5 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval <> retval_2)) (PreH2 : (retval_2 = (expr_eval (e2) (l)))) (PreH3 : (retval = (expr_eval (e1) (l)))) (PreH4 : (v_3 <> 12)) (PreH5 : (v_3 <> 11)) (PreH6 : (e0 = (EBinop (op) (e1) (e2)))) (PreH7 : (v_3 = (BinOpID (op)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 <> e_t)) (PreH11 : (2 = e_t)) (PreH12 : (0 <> v_3)) (PreH13 : (1 <> v_3)) (PreH14 : (2 <> v_3)) (PreH15 : (3 <> v_3)) (PreH16 : (4 <> v_3)) (PreH17 : (5 <> v_3)) (PreH18 : (6 <> v_3)) (PreH19 : (7 <> v_3)) (PreH20 : (8 <> v_3)) (PreH21 : (9 <> v_3)) (PreH22 : (10 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval <> retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 <> v_3)) (PreH24 : (8 <> v_3)) (PreH25 : (9 <> v_3)) (PreH26 : (10 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_5_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval <> retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 <> v_3)) (PreH24 : (8 <> v_3)) (PreH25 : (9 <> v_3)) (PreH26 : (10 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_5_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval <> retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 <> v_3)) (PreH24 : (8 <> v_3)) (PreH25 : (9 <> v_3)) (PreH26 : (10 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_6 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval <> retval_2)) (PreH2 : (retval_2 = (expr_eval (e2) (l)))) (PreH3 : (retval = (expr_eval (e1) (l)))) (PreH4 : (v_3 <> 12)) (PreH5 : (v_3 <> 11)) (PreH6 : (e0 = (EBinop (op) (e1) (e2)))) (PreH7 : (v_3 = (BinOpID (op)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 <> e_t)) (PreH11 : (2 = e_t)) (PreH12 : (0 <> v_3)) (PreH13 : (1 <> v_3)) (PreH14 : (2 <> v_3)) (PreH15 : (3 <> v_3)) (PreH16 : (4 <> v_3)) (PreH17 : (5 <> v_3)) (PreH18 : (6 <> v_3)) (PreH19 : (7 <> v_3)) (PreH20 : (8 <> v_3)) (PreH21 : (9 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval <> retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 <> v_3)) (PreH24 : (8 <> v_3)) (PreH25 : (9 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_6_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval <> retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 <> v_3)) (PreH24 : (8 <> v_3)) (PreH25 : (9 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_6_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval <> retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 <> v_3)) (PreH24 : (8 <> v_3)) (PreH25 : (9 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_7 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (expr_eval (e2) (l)))) (PreH3 : (retval = (expr_eval (e1) (l)))) (PreH4 : (v_3 <> 12)) (PreH5 : (v_3 <> 11)) (PreH6 : (e0 = (EBinop (op) (e1) (e2)))) (PreH7 : (v_3 = (BinOpID (op)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 <> e_t)) (PreH11 : (2 = e_t)) (PreH12 : (0 <> v_3)) (PreH13 : (1 <> v_3)) (PreH14 : (2 <> v_3)) (PreH15 : (3 <> v_3)) (PreH16 : (4 <> v_3)) (PreH17 : (5 <> v_3)) (PreH18 : (6 <> v_3)) (PreH19 : (7 <> v_3)) (PreH20 : (8 <> v_3)) (PreH21 : (9 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 <> v_3)) (PreH24 : (8 <> v_3)) (PreH25 : (9 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_7_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 <> v_3)) (PreH24 : (8 <> v_3)) (PreH25 : (9 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_7_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 <> v_3)) (PreH24 : (8 <> v_3)) (PreH25 : (9 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_8 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (expr_eval (e2) (l)))) (PreH3 : (retval = (expr_eval (e1) (l)))) (PreH4 : (v_3 <> 12)) (PreH5 : (v_3 <> 11)) (PreH6 : (e0 = (EBinop (op) (e1) (e2)))) (PreH7 : (v_3 = (BinOpID (op)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 <> e_t)) (PreH11 : (2 = e_t)) (PreH12 : (0 <> v_3)) (PreH13 : (1 <> v_3)) (PreH14 : (2 <> v_3)) (PreH15 : (3 <> v_3)) (PreH16 : (4 <> v_3)) (PreH17 : (5 <> v_3)) (PreH18 : (6 <> v_3)) (PreH19 : (7 <> v_3)) (PreH20 : (8 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval < retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 <> v_3)) (PreH24 : (8 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_8_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval < retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 <> v_3)) (PreH24 : (8 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_8_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval < retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 <> v_3)) (PreH24 : (8 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_9 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval >= retval_2)) (PreH2 : (retval_2 = (expr_eval (e2) (l)))) (PreH3 : (retval = (expr_eval (e1) (l)))) (PreH4 : (v_3 <> 12)) (PreH5 : (v_3 <> 11)) (PreH6 : (e0 = (EBinop (op) (e1) (e2)))) (PreH7 : (v_3 = (BinOpID (op)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 <> e_t)) (PreH11 : (2 = e_t)) (PreH12 : (0 <> v_3)) (PreH13 : (1 <> v_3)) (PreH14 : (2 <> v_3)) (PreH15 : (3 <> v_3)) (PreH16 : (4 <> v_3)) (PreH17 : (5 <> v_3)) (PreH18 : (6 <> v_3)) (PreH19 : (7 <> v_3)) (PreH20 : (8 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval >= retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 <> v_3)) (PreH24 : (8 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_9_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval >= retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 <> v_3)) (PreH24 : (8 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_9_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval >= retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 <> v_3)) (PreH24 : (8 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_10 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval > retval_2)) (PreH2 : (retval_2 = (expr_eval (e2) (l)))) (PreH3 : (retval = (expr_eval (e1) (l)))) (PreH4 : (v_3 <> 12)) (PreH5 : (v_3 <> 11)) (PreH6 : (e0 = (EBinop (op) (e1) (e2)))) (PreH7 : (v_3 = (BinOpID (op)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 <> e_t)) (PreH11 : (2 = e_t)) (PreH12 : (0 <> v_3)) (PreH13 : (1 <> v_3)) (PreH14 : (2 <> v_3)) (PreH15 : (3 <> v_3)) (PreH16 : (4 <> v_3)) (PreH17 : (5 <> v_3)) (PreH18 : (6 <> v_3)) (PreH19 : (7 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval > retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_10_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval > retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_10_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval > retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_11 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval <= retval_2)) (PreH2 : (retval_2 = (expr_eval (e2) (l)))) (PreH3 : (retval = (expr_eval (e1) (l)))) (PreH4 : (v_3 <> 12)) (PreH5 : (v_3 <> 11)) (PreH6 : (e0 = (EBinop (op) (e1) (e2)))) (PreH7 : (v_3 = (BinOpID (op)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 <> e_t)) (PreH11 : (2 = e_t)) (PreH12 : (0 <> v_3)) (PreH13 : (1 <> v_3)) (PreH14 : (2 <> v_3)) (PreH15 : (3 <> v_3)) (PreH16 : (4 <> v_3)) (PreH17 : (5 <> v_3)) (PreH18 : (6 <> v_3)) (PreH19 : (7 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval <= retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_11_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval <= retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_11_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval <= retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 <> v_3)) (PreH23 : (7 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_12 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval <= retval_2)) (PreH2 : (retval_2 = (expr_eval (e2) (l)))) (PreH3 : (retval = (expr_eval (e1) (l)))) (PreH4 : (v_3 <> 12)) (PreH5 : (v_3 <> 11)) (PreH6 : (e0 = (EBinop (op) (e1) (e2)))) (PreH7 : (v_3 = (BinOpID (op)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 <> e_t)) (PreH11 : (2 = e_t)) (PreH12 : (0 <> v_3)) (PreH13 : (1 <> v_3)) (PreH14 : (2 <> v_3)) (PreH15 : (3 <> v_3)) (PreH16 : (4 <> v_3)) (PreH17 : (5 <> v_3)) (PreH18 : (6 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval <= retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_12_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval <= retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_12_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval <= retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_13 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval > retval_2)) (PreH2 : (retval_2 = (expr_eval (e2) (l)))) (PreH3 : (retval = (expr_eval (e1) (l)))) (PreH4 : (v_3 <> 12)) (PreH5 : (v_3 <> 11)) (PreH6 : (e0 = (EBinop (op) (e1) (e2)))) (PreH7 : (v_3 = (BinOpID (op)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 <> e_t)) (PreH11 : (2 = e_t)) (PreH12 : (0 <> v_3)) (PreH13 : (1 <> v_3)) (PreH14 : (2 <> v_3)) (PreH15 : (3 <> v_3)) (PreH16 : (4 <> v_3)) (PreH17 : (5 <> v_3)) (PreH18 : (6 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval > retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_13_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval > retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_13_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval > retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 <> v_3)) (PreH22 : (6 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_14 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval >= retval_2)) (PreH2 : (retval_2 = (expr_eval (e2) (l)))) (PreH3 : (retval = (expr_eval (e1) (l)))) (PreH4 : (v_3 <> 12)) (PreH5 : (v_3 <> 11)) (PreH6 : (e0 = (EBinop (op) (e1) (e2)))) (PreH7 : (v_3 = (BinOpID (op)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 <> e_t)) (PreH11 : (2 = e_t)) (PreH12 : (0 <> v_3)) (PreH13 : (1 <> v_3)) (PreH14 : (2 <> v_3)) (PreH15 : (3 <> v_3)) (PreH16 : (4 <> v_3)) (PreH17 : (5 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval >= retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_14_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval >= retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_14_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval >= retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_15 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (expr_eval (e2) (l)))) (PreH3 : (retval = (expr_eval (e1) (l)))) (PreH4 : (v_3 <> 12)) (PreH5 : (v_3 <> 11)) (PreH6 : (e0 = (EBinop (op) (e1) (e2)))) (PreH7 : (v_3 = (BinOpID (op)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 <> e_t)) (PreH11 : (2 = e_t)) (PreH12 : (0 <> v_3)) (PreH13 : (1 <> v_3)) (PreH14 : (2 <> v_3)) (PreH15 : (3 <> v_3)) (PreH16 : (4 <> v_3)) (PreH17 : (5 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval < retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_15_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval < retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_15_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval < retval_2)) (PreH6 : (retval_2 = (expr_eval (e2) (l)))) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) (PreH16 : (0 <> v_3)) (PreH17 : (1 <> v_3)) (PreH18 : (2 <> v_3)) (PreH19 : (3 <> v_3)) (PreH20 : (4 <> v_3)) (PreH21 : (5 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_16 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 <> v_3)) (PreH15 : (4 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ ((retval % ( retval_2 ) ) = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 <> 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (0 <> v_3)) (PreH16 : (1 <> v_3)) (PreH17 : (2 <> v_3)) (PreH18 : (3 <> v_3)) (PreH19 : (4 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ ((retval % ( retval_2 ) ) = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_16_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 <> 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (0 <> v_3)) (PreH16 : (1 <> v_3)) (PreH17 : (2 <> v_3)) (PreH18 : (3 <> v_3)) (PreH19 : (4 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ ((retval % ( retval_2 ) ) = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_16_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 <> 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (0 <> v_3)) (PreH16 : (1 <> v_3)) (PreH17 : (2 <> v_3)) (PreH18 : (3 <> v_3)) (PreH19 : (4 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_17 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 <> v_3)) (PreH14 : (3 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ ((retval ÷ retval_2 ) = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 <> 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (0 <> v_3)) (PreH16 : (1 <> v_3)) (PreH17 : (2 <> v_3)) (PreH18 : (3 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ ((retval ÷ retval_2 ) = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_17_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 <> 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (0 <> v_3)) (PreH16 : (1 <> v_3)) (PreH17 : (2 <> v_3)) (PreH18 : (3 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ ((retval ÷ retval_2 ) = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_17_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 <> 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (0 <> v_3)) (PreH16 : (1 <> v_3)) (PreH17 : (2 <> v_3)) (PreH18 : (3 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_18 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 <> v_3)) (PreH13 : (2 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ ((retval * retval_2 ) = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 <> 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (0 <> v_3)) (PreH16 : (1 <> v_3)) (PreH17 : (2 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ ((retval * retval_2 ) = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_18_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 <> 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (0 <> v_3)) (PreH16 : (1 <> v_3)) (PreH17 : (2 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ ((retval * retval_2 ) = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_18_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 <> 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (0 <> v_3)) (PreH16 : (1 <> v_3)) (PreH17 : (2 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_19 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 <> v_3)) (PreH12 : (1 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ ((retval - retval_2 ) = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 <> 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (0 <> v_3)) (PreH16 : (1 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ ((retval - retval_2 ) = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_19_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 <> 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (0 <> v_3)) (PreH16 : (1 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ ((retval - retval_2 ) = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_19_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 <> 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (0 <> v_3)) (PreH16 : (1 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_20 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 <> 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (0 = v_3)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ ((retval + retval_2 ) = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 <> 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (0 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ ((retval + retval_2 ) = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_20_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 <> 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (0 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ ((retval + retval_2 ) = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_20_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 <> 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (0 = v_3)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_21 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 = 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (retval = 0)) (PreH12 : (retval_2 = 0)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 = 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 = 0)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_21_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 = 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 = 0)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_21_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 = 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 = 0)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_22 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 = 12)) (PreH4 : (v_3 <> 11)) (PreH5 : (e0 = (EBinop (op) (e1) (e2)))) (PreH6 : (v_3 = (BinOpID (op)))) (PreH7 : (safe_eval e0 l )) (PreH8 : (0 <> e_t)) (PreH9 : (1 <> e_t)) (PreH10 : (2 = e_t)) (PreH11 : (retval = 0)) (PreH12 : (retval_2 <> 0)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 = 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_22_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 = 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_22_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 = 12)) (PreH8 : (v_3 <> 11)) (PreH9 : (e0 = (EBinop (op) (e1) (e2)))) (PreH10 : (v_3 = (BinOpID (op)))) (PreH11 : (safe_eval e0 l )) (PreH12 : (0 <> e_t)) (PreH13 : (1 <> e_t)) (PreH14 : (2 = e_t)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_23 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (retval = (expr_eval (e1) (l)))) (PreH2 : (v_3 = 12)) (PreH3 : (v_3 <> 11)) (PreH4 : (e0 = (EBinop (op) (e1) (e2)))) (PreH5 : (v_3 = (BinOpID (op)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 <> e_t)) (PreH8 : (1 <> e_t)) (PreH9 : (2 = e_t)) (PreH10 : (retval <> 0)) ,
  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = (expr_eval (e1) (l)))) (PreH6 : (v_3 = 12)) (PreH7 : (v_3 <> 11)) (PreH8 : (e0 = (EBinop (op) (e1) (e2)))) (PreH9 : (v_3 = (BinOpID (op)))) (PreH10 : (safe_eval e0 l )) (PreH11 : (0 <> e_t)) (PreH12 : (1 <> e_t)) (PreH13 : (2 = e_t)) (PreH14 : (retval <> 0)) ,
  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_23_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = (expr_eval (e1) (l)))) (PreH6 : (v_3 = 12)) (PreH7 : (v_3 <> 11)) (PreH8 : (e0 = (EBinop (op) (e1) (e2)))) (PreH9 : (v_3 = (BinOpID (op)))) (PreH10 : (safe_eval e0 l )) (PreH11 : (0 <> e_t)) (PreH12 : (1 <> e_t)) (PreH13 : (2 = e_t)) (PreH14 : (retval <> 0)) ,
  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
|--
  “ (1 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_23_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = (expr_eval (e1) (l)))) (PreH6 : (v_3 = 12)) (PreH7 : (v_3 <> 11)) (PreH8 : (e0 = (EBinop (op) (e1) (e2)))) (PreH9 : (v_3 = (BinOpID (op)))) (PreH10 : (safe_eval e0 l )) (PreH11 : (0 <> e_t)) (PreH12 : (1 <> e_t)) (PreH13 : (2 = e_t)) (PreH14 : (retval <> 0)) ,
  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_24 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (retval = (expr_eval (e1) (l)))) (PreH2 : (v_3 = 11)) (PreH3 : (e0 = (EBinop (op) (e1) (e2)))) (PreH4 : (v_3 = (BinOpID (op)))) (PreH5 : (safe_eval e0 l )) (PreH6 : (0 <> e_t)) (PreH7 : (1 <> e_t)) (PreH8 : (2 = e_t)) (PreH9 : (retval = 0)) ,
  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = (expr_eval (e1) (l)))) (PreH6 : (v_3 = 11)) (PreH7 : (e0 = (EBinop (op) (e1) (e2)))) (PreH8 : (v_3 = (BinOpID (op)))) (PreH9 : (safe_eval e0 l )) (PreH10 : (0 <> e_t)) (PreH11 : (1 <> e_t)) (PreH12 : (2 = e_t)) (PreH13 : (retval = 0)) ,
  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_24_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = (expr_eval (e1) (l)))) (PreH6 : (v_3 = 11)) (PreH7 : (e0 = (EBinop (op) (e1) (e2)))) (PreH8 : (v_3 = (BinOpID (op)))) (PreH9 : (safe_eval e0 l )) (PreH10 : (0 <> e_t)) (PreH11 : (1 <> e_t)) (PreH12 : (2 = e_t)) (PreH13 : (retval = 0)) ,
  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
|--
  “ (0 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_24_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = (expr_eval (e1) (l)))) (PreH6 : (v_3 = 11)) (PreH7 : (e0 = (EBinop (op) (e1) (e2)))) (PreH8 : (v_3 = (BinOpID (op)))) (PreH9 : (safe_eval e0 l )) (PreH10 : (0 <> e_t)) (PreH11 : (1 <> e_t)) (PreH12 : (2 = e_t)) (PreH13 : (retval = 0)) ,
  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_25 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 = 11)) (PreH4 : (e0 = (EBinop (op) (e1) (e2)))) (PreH5 : (v_3 = (BinOpID (op)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 <> e_t)) (PreH8 : (1 <> e_t)) (PreH9 : (2 = e_t)) (PreH10 : (retval <> 0)) (PreH11 : (retval_2 = 0)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 = 11)) (PreH8 : (e0 = (EBinop (op) (e1) (e2)))) (PreH9 : (v_3 = (BinOpID (op)))) (PreH10 : (safe_eval e0 l )) (PreH11 : (0 <> e_t)) (PreH12 : (1 <> e_t)) (PreH13 : (2 = e_t)) (PreH14 : (retval <> 0)) (PreH15 : (retval_2 = 0)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_25_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 = 11)) (PreH8 : (e0 = (EBinop (op) (e1) (e2)))) (PreH9 : (v_3 = (BinOpID (op)))) (PreH10 : (safe_eval e0 l )) (PreH11 : (0 <> e_t)) (PreH12 : (1 <> e_t)) (PreH13 : (2 = e_t)) (PreH14 : (retval <> 0)) (PreH15 : (retval_2 = 0)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (0 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_25_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 = 11)) (PreH8 : (e0 = (EBinop (op) (e1) (e2)))) (PreH9 : (v_3 = (BinOpID (op)))) (PreH10 : (safe_eval e0 l )) (PreH11 : (0 <> e_t)) (PreH12 : (1 <> e_t)) (PreH13 : (2 = e_t)) (PreH14 : (retval <> 0)) (PreH15 : (retval_2 = 0)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_26 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (expr_eval (e2) (l)))) (PreH2 : (retval = (expr_eval (e1) (l)))) (PreH3 : (v_3 = 11)) (PreH4 : (e0 = (EBinop (op) (e1) (e2)))) (PreH5 : (v_3 = (BinOpID (op)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 <> e_t)) (PreH8 : (1 <> e_t)) (PreH9 : (2 = e_t)) (PreH10 : (retval <> 0)) (PreH11 : (retval_2 <> 0)) ,
  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 = 11)) (PreH8 : (e0 = (EBinop (op) (e1) (e2)))) (PreH9 : (v_3 = (BinOpID (op)))) (PreH10 : (safe_eval e0 l )) (PreH11 : (0 <> e_t)) (PreH12 : (1 <> e_t)) (PreH13 : (2 = e_t)) (PreH14 : (retval <> 0)) (PreH15 : (retval_2 <> 0)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_26_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 = 11)) (PreH8 : (e0 = (EBinop (op) (e1) (e2)))) (PreH9 : (v_3 = (BinOpID (op)))) (PreH10 : (safe_eval e0 l )) (PreH11 : (0 <> e_t)) (PreH12 : (1 <> e_t)) (PreH13 : (2 = e_t)) (PreH14 : (retval <> 0)) (PreH15 : (retval_2 <> 0)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  “ (1 = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_26_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (retval_2: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval_2 = (expr_eval (e2) (l)))) (PreH6 : (retval = (expr_eval (e1) (l)))) (PreH7 : (v_3 = 11)) (PreH8 : (e0 = (EBinop (op) (e1) (e2)))) (PreH9 : (v_3 = (BinOpID (op)))) (PreH10 : (safe_eval e0 l )) (PreH11 : (0 <> e_t)) (PreH12 : (1 <> e_t)) (PreH13 : (2 = e_t)) (PreH14 : (retval <> 0)) (PreH15 : (retval_2 <> 0)) ,
  (store_expr v e2 )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_27 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (n: Z) (PreH1 : (0 <= n)) (PreH2 : (n < 100)) (PreH3 : (e0 = (EVar (n)))) (PreH4 : (safe_eval e0 l )) (PreH5 : (0 <> e_t)) (PreH6 : (1 = e_t)) ,
  (IntArray.full var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 1)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ ((Znth n l 0) = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (n: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (0 <= n)) (PreH6 : (n < 100)) (PreH7 : (e0 = (EVar (n)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 = e_t)) ,
  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 1)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ ((Znth n l 0) = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_27_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (n: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (0 <= n)) (PreH6 : (n < 100)) (PreH7 : (e0 = (EVar (n)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 = e_t)) ,
  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 1)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ ((Znth n l 0) = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_27_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (n: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (0 <= n)) (PreH6 : (n < 100)) (PreH7 : (e0 = (EVar (n)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 = e_t)) ,
  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 1)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  (store_expr e_pre e0 )
.

Definition eval_return_wit_28 := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (n: Z) (PreH1 : (0 = 0)) (PreH2 : (e0 = (EConst (n)))) (PreH3 : (safe_eval e0 l )) (PreH4 : (0 = e_t)) ,
  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 0)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "CONST" .ₛ "value")) # Int  |-> n)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (n = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
) \/
(
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (n: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (e0 = (EConst (n)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 = e_t)) ,
  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 0)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "CONST" .ₛ "value")) # Int  |-> n)
|--
  “ (n = (expr_eval (e0) (l))) ”
  &&  (store_expr e_pre e0 )
).

Definition eval_return_wit_28_split_goal_1 := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (n: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (e0 = (EConst (n)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 = e_t)) ,
  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 0)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "CONST" .ₛ "value")) # Int  |-> n)
|--
  “ (n = (expr_eval (e0) (l))) ”
.

Definition eval_return_wit_28_split_goal_spatial := 
forall (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (n: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (e0 = (EConst (n)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 = e_t)) ,
  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 0)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "CONST" .ₛ "value")) # Int  |-> n)
|--
  (store_expr e_pre e0 )
.

Definition eval_partial_solve_wit_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (PreH1 : (safe_eval e0 l )) ,
  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e0 l ) ”
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_partial_solve_wit_2_pure := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (PreH1 : (safe_eval e0 l )) (PreH2 : (0 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (0 = 0) ”
.

Definition eval_partial_solve_wit_2_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (PreH1 : (safe_eval e0 l )) (PreH2 : (0 = e_t)) ,
  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (0 = 0) ” 
  &&  “ (safe_eval e0 l ) ” 
  &&  “ (0 = e_t) ”
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 0)
  **  (store_expr_aux e_pre 0 e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_partial_solve_wit_2 := eval_partial_solve_wit_2_pure -> eval_partial_solve_wit_2_aux.

Definition eval_partial_solve_wit_3_pure := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (PreH1 : (safe_eval e0 l )) (PreH2 : (0 <> e_t)) (PreH3 : (1 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (1 = 1) ” 
  &&  “ (safe_eval e0 l ) ”
.

Definition eval_partial_solve_wit_3_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (PreH1 : (safe_eval e0 l )) (PreH2 : (0 <> e_t)) (PreH3 : (1 = e_t)) ,
  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (1 = 1) ” 
  &&  “ (safe_eval e0 l ) ” 
  &&  “ (safe_eval e0 l ) ” 
  &&  “ (0 <> e_t) ” 
  &&  “ (1 = e_t) ”
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 1)
  **  (store_expr_aux e_pre 1 e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_partial_solve_wit_3 := eval_partial_solve_wit_3_pure -> eval_partial_solve_wit_3_aux.

Definition eval_partial_solve_wit_4 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (n: Z) (PreH1 : (0 <= n)) (PreH2 : (n < 100)) (PreH3 : (1 = 1)) (PreH4 : (e0 = (EVar (n)))) (PreH5 : (safe_eval e0 l )) (PreH6 : (0 <> e_t)) (PreH7 : (1 = e_t)) ,
  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 1)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (e0 = (EVar (n))) ” 
  &&  “ (safe_eval e0 l ) ” 
  &&  “ (0 <> e_t) ” 
  &&  “ (1 = e_t) ”
  &&  (((var_value_pre + (n * sizeof(INT)))) # Int  |-> (Znth n l 0))
  **  (IntArray.missing_i var_value_pre n 0 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 1)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition eval_partial_solve_wit_5_pure := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (PreH1 : (safe_eval e0 l )) (PreH2 : (0 <> e_t)) (PreH3 : (1 <> e_t)) (PreH4 : (2 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (2 = 2) ”
.

Definition eval_partial_solve_wit_5_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (PreH1 : (safe_eval e0 l )) (PreH2 : (0 <> e_t)) (PreH3 : (1 <> e_t)) (PreH4 : (2 = e_t)) ,
  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (2 = 2) ” 
  &&  “ (safe_eval e0 l ) ” 
  &&  “ (0 <> e_t) ” 
  &&  “ (1 <> e_t) ” 
  &&  “ (2 = e_t) ”
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  (store_expr_aux e_pre 2 e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_partial_solve_wit_5 := eval_partial_solve_wit_5_pure -> eval_partial_solve_wit_5_aux.

Definition eval_partial_solve_wit_6_pure := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (PreH1 : (v_3 = 11)) (PreH2 : (2 = 2)) (PreH3 : (e0 = (EBinop (op) (e1) (e2)))) (PreH4 : (v_3 = (BinOpID (op)))) (PreH5 : (safe_eval e0 l )) (PreH6 : (0 <> e_t)) (PreH7 : (1 <> e_t)) (PreH8 : (2 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ”
) \/
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (v_3 = 11)) (PreH6 : (e0 = (EBinop (op) (e1) (e2)))) (PreH7 : (v_3 = (BinOpID (op)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 <> e_t)) (PreH11 : (2 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ”
).

Definition eval_partial_solve_wit_6_pure_split_goal_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (v_3 = 11)) (PreH6 : (e0 = (EBinop (op) (e1) (e2)))) (PreH7 : (v_3 = (BinOpID (op)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 <> e_t)) (PreH11 : (2 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ”
.

Definition eval_partial_solve_wit_6_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (PreH1 : (v_3 = 11)) (PreH2 : (2 = 2)) (PreH3 : (e0 = (EBinop (op) (e1) (e2)))) (PreH4 : (v_3 = (BinOpID (op)))) (PreH5 : (safe_eval e0 l )) (PreH6 : (0 <> e_t)) (PreH7 : (1 <> e_t)) (PreH8 : (2 = e_t)) ,
  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ” 
  &&  “ (v_3 = 11) ” 
  &&  “ (e0 = (EBinop (op) (e1) (e2))) ” 
  &&  “ (v_3 = (BinOpID (op))) ” 
  &&  “ (safe_eval e0 l ) ” 
  &&  “ (0 <> e_t) ” 
  &&  “ (1 <> e_t) ” 
  &&  “ (2 = e_t) ”
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
.

Definition eval_partial_solve_wit_6 := eval_partial_solve_wit_6_pure -> eval_partial_solve_wit_6_aux.

Definition eval_partial_solve_wit_7_pure := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (retval = (expr_eval (e1) (l)))) (PreH2 : (v_3 = 11)) (PreH3 : (e0 = (EBinop (op) (e1) (e2)))) (PreH4 : (v_3 = (BinOpID (op)))) (PreH5 : (safe_eval e0 l )) (PreH6 : (0 <> e_t)) (PreH7 : (1 <> e_t)) (PreH8 : (2 = e_t)) (PreH9 : (retval <> 0)) ,
  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (safe_eval e2 l ) ”
) \/
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = (expr_eval (e1) (l)))) (PreH6 : (v_3 = 11)) (PreH7 : (e0 = (EBinop (op) (e1) (e2)))) (PreH8 : (v_3 = (BinOpID (op)))) (PreH9 : (safe_eval e0 l )) (PreH10 : (0 <> e_t)) (PreH11 : (1 <> e_t)) (PreH12 : (2 = e_t)) (PreH13 : (retval <> 0)) ,
  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (safe_eval e2 l ) ”
).

Definition eval_partial_solve_wit_7_pure_split_goal_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = (expr_eval (e1) (l)))) (PreH6 : (v_3 = 11)) (PreH7 : (e0 = (EBinop (op) (e1) (e2)))) (PreH8 : (v_3 = (BinOpID (op)))) (PreH9 : (safe_eval e0 l )) (PreH10 : (0 <> e_t)) (PreH11 : (1 <> e_t)) (PreH12 : (2 = e_t)) (PreH13 : (retval <> 0)) ,
  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (safe_eval e2 l ) ”
.

Definition eval_partial_solve_wit_7_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (retval = (expr_eval (e1) (l)))) (PreH2 : (v_3 = 11)) (PreH3 : (e0 = (EBinop (op) (e1) (e2)))) (PreH4 : (v_3 = (BinOpID (op)))) (PreH5 : (safe_eval e0 l )) (PreH6 : (0 <> e_t)) (PreH7 : (1 <> e_t)) (PreH8 : (2 = e_t)) (PreH9 : (retval <> 0)) ,
  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
|--
  “ (safe_eval e2 l ) ” 
  &&  “ (retval = (expr_eval (e1) (l))) ” 
  &&  “ (v_3 = 11) ” 
  &&  “ (e0 = (EBinop (op) (e1) (e2))) ” 
  &&  “ (v_3 = (BinOpID (op))) ” 
  &&  “ (safe_eval e0 l ) ” 
  &&  “ (0 <> e_t) ” 
  &&  “ (1 <> e_t) ” 
  &&  “ (2 = e_t) ” 
  &&  “ (retval <> 0) ”
  &&  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
.

Definition eval_partial_solve_wit_7 := eval_partial_solve_wit_7_pure -> eval_partial_solve_wit_7_aux.

Definition eval_partial_solve_wit_8_pure := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (PreH1 : (v_3 = 12)) (PreH2 : (v_3 <> 11)) (PreH3 : (2 = 2)) (PreH4 : (e0 = (EBinop (op) (e1) (e2)))) (PreH5 : (v_3 = (BinOpID (op)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 <> e_t)) (PreH8 : (1 <> e_t)) (PreH9 : (2 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ”
) \/
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (v_3 = 12)) (PreH6 : (v_3 <> 11)) (PreH7 : (e0 = (EBinop (op) (e1) (e2)))) (PreH8 : (v_3 = (BinOpID (op)))) (PreH9 : (safe_eval e0 l )) (PreH10 : (0 <> e_t)) (PreH11 : (1 <> e_t)) (PreH12 : (2 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ”
).

Definition eval_partial_solve_wit_8_pure_split_goal_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (v_3 = 12)) (PreH6 : (v_3 <> 11)) (PreH7 : (e0 = (EBinop (op) (e1) (e2)))) (PreH8 : (v_3 = (BinOpID (op)))) (PreH9 : (safe_eval e0 l )) (PreH10 : (0 <> e_t)) (PreH11 : (1 <> e_t)) (PreH12 : (2 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ”
.

Definition eval_partial_solve_wit_8_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (PreH1 : (v_3 = 12)) (PreH2 : (v_3 <> 11)) (PreH3 : (2 = 2)) (PreH4 : (e0 = (EBinop (op) (e1) (e2)))) (PreH5 : (v_3 = (BinOpID (op)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 <> e_t)) (PreH8 : (1 <> e_t)) (PreH9 : (2 = e_t)) ,
  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ” 
  &&  “ (v_3 = 12) ” 
  &&  “ (v_3 <> 11) ” 
  &&  “ (e0 = (EBinop (op) (e1) (e2))) ” 
  &&  “ (v_3 = (BinOpID (op))) ” 
  &&  “ (safe_eval e0 l ) ” 
  &&  “ (0 <> e_t) ” 
  &&  “ (1 <> e_t) ” 
  &&  “ (2 = e_t) ”
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
.

Definition eval_partial_solve_wit_8 := eval_partial_solve_wit_8_pure -> eval_partial_solve_wit_8_aux.

Definition eval_partial_solve_wit_9_pure := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (retval = (expr_eval (e1) (l)))) (PreH2 : (v_3 = 12)) (PreH3 : (v_3 <> 11)) (PreH4 : (e0 = (EBinop (op) (e1) (e2)))) (PreH5 : (v_3 = (BinOpID (op)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 <> e_t)) (PreH8 : (1 <> e_t)) (PreH9 : (2 = e_t)) (PreH10 : (retval = 0)) ,
  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (safe_eval e2 l ) ”
) \/
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = (expr_eval (e1) (l)))) (PreH6 : (v_3 = 12)) (PreH7 : (v_3 <> 11)) (PreH8 : (e0 = (EBinop (op) (e1) (e2)))) (PreH9 : (v_3 = (BinOpID (op)))) (PreH10 : (safe_eval e0 l )) (PreH11 : (0 <> e_t)) (PreH12 : (1 <> e_t)) (PreH13 : (2 = e_t)) (PreH14 : (retval = 0)) ,
  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (safe_eval e2 l ) ”
).

Definition eval_partial_solve_wit_9_pure_split_goal_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = (expr_eval (e1) (l)))) (PreH6 : (v_3 = 12)) (PreH7 : (v_3 <> 11)) (PreH8 : (e0 = (EBinop (op) (e1) (e2)))) (PreH9 : (v_3 = (BinOpID (op)))) (PreH10 : (safe_eval e0 l )) (PreH11 : (0 <> e_t)) (PreH12 : (1 <> e_t)) (PreH13 : (2 = e_t)) (PreH14 : (retval = 0)) ,
  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (safe_eval e2 l ) ”
.

Definition eval_partial_solve_wit_9_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (retval = (expr_eval (e1) (l)))) (PreH2 : (v_3 = 12)) (PreH3 : (v_3 <> 11)) (PreH4 : (e0 = (EBinop (op) (e1) (e2)))) (PreH5 : (v_3 = (BinOpID (op)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 <> e_t)) (PreH8 : (1 <> e_t)) (PreH9 : (2 = e_t)) (PreH10 : (retval = 0)) ,
  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
|--
  “ (safe_eval e2 l ) ” 
  &&  “ (retval = (expr_eval (e1) (l))) ” 
  &&  “ (v_3 = 12) ” 
  &&  “ (v_3 <> 11) ” 
  &&  “ (e0 = (EBinop (op) (e1) (e2))) ” 
  &&  “ (v_3 = (BinOpID (op))) ” 
  &&  “ (safe_eval e0 l ) ” 
  &&  “ (0 <> e_t) ” 
  &&  “ (1 <> e_t) ” 
  &&  “ (2 = e_t) ” 
  &&  “ (retval = 0) ”
  &&  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
.

Definition eval_partial_solve_wit_9 := eval_partial_solve_wit_9_pure -> eval_partial_solve_wit_9_aux.

Definition eval_partial_solve_wit_10_pure := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (PreH1 : (v_3 <> 12)) (PreH2 : (v_3 <> 11)) (PreH3 : (2 = 2)) (PreH4 : (e0 = (EBinop (op) (e1) (e2)))) (PreH5 : (v_3 = (BinOpID (op)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 <> e_t)) (PreH8 : (1 <> e_t)) (PreH9 : (2 = e_t)) ,
  ((( &( "left_val" ) )) # Int  |->_)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ”
) \/
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (v_3 <> 12)) (PreH6 : (v_3 <> 11)) (PreH7 : (e0 = (EBinop (op) (e1) (e2)))) (PreH8 : (v_3 = (BinOpID (op)))) (PreH9 : (safe_eval e0 l )) (PreH10 : (0 <> e_t)) (PreH11 : (1 <> e_t)) (PreH12 : (2 = e_t)) ,
  ((( &( "left_val" ) )) # Int  |->_)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ”
).

Definition eval_partial_solve_wit_10_pure_split_goal_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (v_3 >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (v_3 <> 12)) (PreH6 : (v_3 <> 11)) (PreH7 : (e0 = (EBinop (op) (e1) (e2)))) (PreH8 : (v_3 = (BinOpID (op)))) (PreH9 : (safe_eval e0 l )) (PreH10 : (0 <> e_t)) (PreH11 : (1 <> e_t)) (PreH12 : (2 = e_t)) ,
  ((( &( "left_val" ) )) # Int  |->_)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ”
.

Definition eval_partial_solve_wit_10_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (PreH1 : (v_3 <> 12)) (PreH2 : (v_3 <> 11)) (PreH3 : (2 = 2)) (PreH4 : (e0 = (EBinop (op) (e1) (e2)))) (PreH5 : (v_3 = (BinOpID (op)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 <> e_t)) (PreH8 : (1 <> e_t)) (PreH9 : (2 = e_t)) ,
  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ” 
  &&  “ (v_3 <> 12) ” 
  &&  “ (v_3 <> 11) ” 
  &&  “ (e0 = (EBinop (op) (e1) (e2))) ” 
  &&  “ (v_3 = (BinOpID (op))) ” 
  &&  “ (safe_eval e0 l ) ” 
  &&  “ (0 <> e_t) ” 
  &&  “ (1 <> e_t) ” 
  &&  “ (2 = e_t) ”
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
.

Definition eval_partial_solve_wit_10 := eval_partial_solve_wit_10_pure -> eval_partial_solve_wit_10_aux.

Definition eval_partial_solve_wit_11_pure := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (retval = (expr_eval (e1) (l)))) (PreH2 : (v_3 <> 12)) (PreH3 : (v_3 <> 11)) (PreH4 : (e0 = (EBinop (op) (e1) (e2)))) (PreH5 : (v_3 = (BinOpID (op)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 <> e_t)) (PreH8 : (1 <> e_t)) (PreH9 : (2 = e_t)) ,
  ((( &( "right_val" ) )) # Int  |->_)
  **  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (safe_eval e2 l ) ”
) \/
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (retval <= INT_MAX)) (PreH4 : (v_3 >= INT_MIN)) (PreH5 : (2 >= INT_MIN)) (PreH6 : (retval >= INT_MIN)) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) ,
  ((( &( "right_val" ) )) # Int  |->_)
  **  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (safe_eval e2 l ) ”
).

Definition eval_partial_solve_wit_11_pure_split_goal_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (v_3 <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (retval <= INT_MAX)) (PreH4 : (v_3 >= INT_MIN)) (PreH5 : (2 >= INT_MIN)) (PreH6 : (retval >= INT_MIN)) (PreH7 : (retval = (expr_eval (e1) (l)))) (PreH8 : (v_3 <> 12)) (PreH9 : (v_3 <> 11)) (PreH10 : (e0 = (EBinop (op) (e1) (e2)))) (PreH11 : (v_3 = (BinOpID (op)))) (PreH12 : (safe_eval e0 l )) (PreH13 : (0 <> e_t)) (PreH14 : (1 <> e_t)) (PreH15 : (2 = e_t)) ,
  ((( &( "right_val" ) )) # Int  |->_)
  **  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
|--
  “ (safe_eval e2 l ) ”
.

Definition eval_partial_solve_wit_11_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (v_3: Z) (op: binop) (e1: expr) (e2: expr) (retval: Z) (PreH1 : (retval = (expr_eval (e1) (l)))) (PreH2 : (v_3 <> 12)) (PreH3 : (v_3 <> 11)) (PreH4 : (e0 = (EBinop (op) (e1) (e2)))) (PreH5 : (v_3 = (BinOpID (op)))) (PreH6 : (safe_eval e0 l )) (PreH7 : (0 <> e_t)) (PreH8 : (1 <> e_t)) (PreH9 : (2 = e_t)) ,
  (store_expr v_2 e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
  **  (store_expr v e2 )
|--
  “ (safe_eval e2 l ) ” 
  &&  “ (retval = (expr_eval (e1) (l))) ” 
  &&  “ (v_3 <> 12) ” 
  &&  “ (v_3 <> 11) ” 
  &&  “ (e0 = (EBinop (op) (e1) (e2))) ” 
  &&  “ (v_3 = (BinOpID (op))) ” 
  &&  “ (safe_eval e0 l ) ” 
  &&  “ (0 <> e_t) ” 
  &&  “ (1 <> e_t) ” 
  &&  “ (2 = e_t) ”
  &&  (store_expr v e2 )
  **  (IntArray.full var_value_pre 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v_3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v)
.

Definition eval_partial_solve_wit_11 := eval_partial_solve_wit_11_pure -> eval_partial_solve_wit_11_aux.

Definition eval_partial_solve_wit_12_pure := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (PreH1 : (safe_eval e0 l )) (PreH2 : (0 <> e_t)) (PreH3 : (1 <> e_t)) (PreH4 : (2 <> e_t)) (PreH5 : (3 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (3 = 3) ”
.

Definition eval_partial_solve_wit_12_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (PreH1 : (safe_eval e0 l )) (PreH2 : (0 <> e_t)) (PreH3 : (1 <> e_t)) (PreH4 : (2 <> e_t)) (PreH5 : (3 = e_t)) ,
  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (3 = 3) ” 
  &&  “ (safe_eval e0 l ) ” 
  &&  “ (0 <> e_t) ” 
  &&  “ (1 <> e_t) ” 
  &&  “ (2 <> e_t) ” 
  &&  “ (3 = e_t) ”
  &&  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  (store_expr_aux e_pre 3 e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_partial_solve_wit_12 := eval_partial_solve_wit_12_pure -> eval_partial_solve_wit_12_aux.

Definition eval_partial_solve_wit_13_pure := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (PreH1 : (v_2 = 1)) (PreH2 : (3 = 3)) (PreH3 : (e0 = (EUnop (op) (e1)))) (PreH4 : (v_2 = (UnOpID (op)))) (PreH5 : (safe_eval e0 l )) (PreH6 : (0 <> e_t)) (PreH7 : (1 <> e_t)) (PreH8 : (2 <> e_t)) (PreH9 : (3 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  (store_expr v e1 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ”
) \/
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (v_2 >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : (v_2 = 1)) (PreH6 : (e0 = (EUnop (op) (e1)))) (PreH7 : (v_2 = (UnOpID (op)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 <> e_t)) (PreH11 : (2 <> e_t)) (PreH12 : (3 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  (store_expr v e1 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ”
).

Definition eval_partial_solve_wit_13_pure_split_goal_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (v_2 >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : (v_2 = 1)) (PreH6 : (e0 = (EUnop (op) (e1)))) (PreH7 : (v_2 = (UnOpID (op)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 <> e_t)) (PreH11 : (2 <> e_t)) (PreH12 : (3 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  (store_expr v e1 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ”
.

Definition eval_partial_solve_wit_13_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (PreH1 : (v_2 = 1)) (PreH2 : (3 = 3)) (PreH3 : (e0 = (EUnop (op) (e1)))) (PreH4 : (v_2 = (UnOpID (op)))) (PreH5 : (safe_eval e0 l )) (PreH6 : (0 <> e_t)) (PreH7 : (1 <> e_t)) (PreH8 : (2 <> e_t)) (PreH9 : (3 = e_t)) ,
  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  (store_expr v e1 )
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ” 
  &&  “ (v_2 = 1) ” 
  &&  “ (e0 = (EUnop (op) (e1))) ” 
  &&  “ (v_2 = (UnOpID (op))) ” 
  &&  “ (safe_eval e0 l ) ” 
  &&  “ (0 <> e_t) ” 
  &&  “ (1 <> e_t) ” 
  &&  “ (2 <> e_t) ” 
  &&  “ (3 = e_t) ”
  &&  (store_expr v e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
.

Definition eval_partial_solve_wit_13 := eval_partial_solve_wit_13_pure -> eval_partial_solve_wit_13_aux.

Definition eval_partial_solve_wit_14_pure := 
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (PreH1 : (v_2 <> 1)) (PreH2 : (3 = 3)) (PreH3 : (e0 = (EUnop (op) (e1)))) (PreH4 : (v_2 = (UnOpID (op)))) (PreH5 : (safe_eval e0 l )) (PreH6 : (0 <> e_t)) (PreH7 : (1 <> e_t)) (PreH8 : (2 <> e_t)) (PreH9 : (3 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  (store_expr v e1 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ”
) \/
(
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (v_2 >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : (v_2 <> 1)) (PreH6 : (e0 = (EUnop (op) (e1)))) (PreH7 : (v_2 = (UnOpID (op)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 <> e_t)) (PreH11 : (2 <> e_t)) (PreH12 : (3 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  (store_expr v e1 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ”
).

Definition eval_partial_solve_wit_14_pure_split_goal_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (v_2 >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : (v_2 <> 1)) (PreH6 : (e0 = (EUnop (op) (e1)))) (PreH7 : (v_2 = (UnOpID (op)))) (PreH8 : (safe_eval e0 l )) (PreH9 : (0 <> e_t)) (PreH10 : (1 <> e_t)) (PreH11 : (2 <> e_t)) (PreH12 : (3 = e_t)) ,
  ((( &( "e" ) )) # Ptr  |-> e_pre)
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  (store_expr v e1 )
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value_pre)
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ”
.

Definition eval_partial_solve_wit_14_aux := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e_t: Z) (v: Z) (v_2: Z) (op: unop) (e1: expr) (PreH1 : (v_2 <> 1)) (PreH2 : (3 = 3)) (PreH3 : (e0 = (EUnop (op) (e1)))) (PreH4 : (v_2 = (UnOpID (op)))) (PreH5 : (safe_eval e0 l )) (PreH6 : (0 <> e_t)) (PreH7 : (1 <> e_t)) (PreH8 : (2 <> e_t)) (PreH9 : (3 = e_t)) ,
  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
  **  (store_expr v e1 )
  **  (IntArray.full var_value_pre 100 l )
|--
  “ (safe_eval e1 l ) ” 
  &&  “ (v_2 <> 1) ” 
  &&  “ (e0 = (EUnop (op) (e1))) ” 
  &&  “ (v_2 = (UnOpID (op))) ” 
  &&  “ (safe_eval e0 l ) ” 
  &&  “ (0 <> e_t) ” 
  &&  “ (1 <> e_t) ” 
  &&  “ (2 <> e_t) ” 
  &&  “ (3 = e_t) ”
  &&  (store_expr v e1 )
  **  (IntArray.full var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> 3)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v_2)
  **  ((&((e_pre)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v)
.

Definition eval_partial_solve_wit_14 := eval_partial_solve_wit_14_pure -> eval_partial_solve_wit_14_aux.

Definition eval_which_implies_wit_1 := 
(
forall (e0: expr) (e: Z) ,
  (store_expr e e0 )
|--
  EX (e_t: Z) ,
  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e e_t e0 )
) \/
(
forall (e0: expr) (e: Z) ,
  (store_expr e e0 )
|--
  EX (e_t: Z) ,
  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e e_t e0 )
).

Definition eval_which_implies_wit_2 := 
(
forall (e0: expr) (e: Z) (e_t: Z) (PreH1 : (e_t = 0)) ,
  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e e_t e0 )
|--
  EX (n: Z) ,
  “ (e_t = 0) ” 
  &&  “ (e0 = (EConst (n))) ”
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "CONST" .ₛ "value")) # Int  |-> n)
) \/
(
forall (e0: expr) (e: Z) (e_t: Z) (PreH1 : (e_t = 0)) ,
  (store_expr_aux e e_t e0 )
|--
  EX (n: Z) ,
  “ (e_t = 0) ” 
  &&  “ (e0 = (EConst (n))) ”
  &&  ((&((e)  # "expr" ->ₛ "d" .ₛ "CONST" .ₛ "value")) # Int  |-> n)
).

Definition eval_which_implies_wit_3 := 
(
forall (l: (@list Z)) (e0: expr) (e: Z) (e_t: Z) (var_value: Z) (PreH1 : (e_t = 1)) (PreH2 : (safe_eval e0 l )) ,
  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e e_t e0 )
  **  (IntArray.full var_value 100 l )
|--
  EX (n: Z) ,
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (e_t = 1) ” 
  &&  “ (e0 = (EVar (n))) ”
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (IntArray.full var_value 100 l )
) \/
(
forall (l: (@list Z)) (e0: expr) (e: Z) (e_t: Z) (PreH1 : (e_t = 1)) (PreH2 : (safe_eval e0 l )) ,
  (store_expr_aux e e_t e0 )
|--
  EX (n: Z) ,
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (e_t = 1) ” 
  &&  “ (e0 = (EVar (n))) ”
  &&  ((&((e)  # "expr" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
).

Definition eval_which_implies_wit_4 := 
(
forall (e0: expr) (e: Z) (e_t: Z) (PreH1 : (e_t = 2)) ,
  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e e_t e0 )
|--
  EX (v_3: Z)  (v_2: Z)  (v: Z)  (op: binop)  (e1: expr)  (e2: expr) ,
  “ (e_t = 2) ” 
  &&  “ (e0 = (EBinop (op) (e1) (e2))) ” 
  &&  “ (v = (BinOpID (op))) ”
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
) \/
(
forall (e0: expr) (e: Z) (e_t: Z) (PreH1 : (e_t = 2)) ,
  (store_expr_aux e e_t e0 )
|--
  EX (v_3: Z)  (v_2: Z)  (op: binop)  (e1: expr)  (e2: expr) ,
  “ (e_t = 2) ” 
  &&  “ (e0 = (EBinop (op) (e1) (e2))) ”
  &&  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> (BinOpID (op)))
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
).

Definition eval_which_implies_wit_5 := 
(
forall (e0: expr) (e: Z) (e_t: Z) (PreH1 : (e_t = 3)) ,
  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e e_t e0 )
|--
  EX (v_2: Z)  (v: Z)  (op: unop)  (e1: expr) ,
  “ (e_t = 3) ” 
  &&  “ (e0 = (EUnop (op) (e1))) ” 
  &&  “ (v = (UnOpID (op))) ”
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
) \/
(
forall (e0: expr) (e: Z) (e_t: Z) (PreH1 : (e_t = 3)) ,
  (store_expr_aux e e_t e0 )
|--
  EX (v_2: Z)  (op: unop)  (e1: expr) ,
  “ (e_t = 3) ” 
  &&  “ (e0 = (EUnop (op) (e1))) ”
  &&  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> (UnOpID (op)))
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
).

Module Type VC_Correct.

Include eval_Strategy_Correct.

Axiom proof_of_eval_safety_wit_1 : eval_safety_wit_1.
Axiom proof_of_eval_safety_wit_2 : eval_safety_wit_2.
Axiom proof_of_eval_safety_wit_3 : eval_safety_wit_3.
Axiom proof_of_eval_safety_wit_4 : eval_safety_wit_4.
Axiom proof_of_eval_safety_wit_5 : eval_safety_wit_5.
Axiom proof_of_eval_safety_wit_6 : eval_safety_wit_6.
Axiom proof_of_eval_safety_wit_7 : eval_safety_wit_7.
Axiom proof_of_eval_safety_wit_8 : eval_safety_wit_8.
Axiom proof_of_eval_safety_wit_9 : eval_safety_wit_9.
Axiom proof_of_eval_safety_wit_10 : eval_safety_wit_10.
Axiom proof_of_eval_safety_wit_11 : eval_safety_wit_11.
Axiom proof_of_eval_safety_wit_12 : eval_safety_wit_12.
Axiom proof_of_eval_safety_wit_13 : eval_safety_wit_13.
Axiom proof_of_eval_safety_wit_14 : eval_safety_wit_14.
Axiom proof_of_eval_safety_wit_15 : eval_safety_wit_15.
Axiom proof_of_eval_safety_wit_16 : eval_safety_wit_16.
Axiom proof_of_eval_safety_wit_17 : eval_safety_wit_17.
Axiom proof_of_eval_safety_wit_18 : eval_safety_wit_18.
Axiom proof_of_eval_safety_wit_19 : eval_safety_wit_19.
Axiom proof_of_eval_safety_wit_20 : eval_safety_wit_20.
Axiom proof_of_eval_safety_wit_21 : eval_safety_wit_21.
Axiom proof_of_eval_safety_wit_22 : eval_safety_wit_22.
Axiom proof_of_eval_safety_wit_23 : eval_safety_wit_23.
Axiom proof_of_eval_safety_wit_24 : eval_safety_wit_24.
Axiom proof_of_eval_safety_wit_25 : eval_safety_wit_25.
Axiom proof_of_eval_safety_wit_26 : eval_safety_wit_26.
Axiom proof_of_eval_safety_wit_27 : eval_safety_wit_27.
Axiom proof_of_eval_safety_wit_28 : eval_safety_wit_28.
Axiom proof_of_eval_safety_wit_29 : eval_safety_wit_29.
Axiom proof_of_eval_safety_wit_30 : eval_safety_wit_30.
Axiom proof_of_eval_safety_wit_31 : eval_safety_wit_31.
Axiom proof_of_eval_safety_wit_32 : eval_safety_wit_32.
Axiom proof_of_eval_return_wit_1 : eval_return_wit_1.
Axiom proof_of_eval_return_wit_2 : eval_return_wit_2.
Axiom proof_of_eval_return_wit_3 : eval_return_wit_3.
Axiom proof_of_eval_return_wit_4 : eval_return_wit_4.
Axiom proof_of_eval_return_wit_5 : eval_return_wit_5.
Axiom proof_of_eval_return_wit_6 : eval_return_wit_6.
Axiom proof_of_eval_return_wit_7 : eval_return_wit_7.
Axiom proof_of_eval_return_wit_8 : eval_return_wit_8.
Axiom proof_of_eval_return_wit_9 : eval_return_wit_9.
Axiom proof_of_eval_return_wit_10 : eval_return_wit_10.
Axiom proof_of_eval_return_wit_11 : eval_return_wit_11.
Axiom proof_of_eval_return_wit_12 : eval_return_wit_12.
Axiom proof_of_eval_return_wit_13 : eval_return_wit_13.
Axiom proof_of_eval_return_wit_14 : eval_return_wit_14.
Axiom proof_of_eval_return_wit_15 : eval_return_wit_15.
Axiom proof_of_eval_return_wit_16 : eval_return_wit_16.
Axiom proof_of_eval_return_wit_17 : eval_return_wit_17.
Axiom proof_of_eval_return_wit_18 : eval_return_wit_18.
Axiom proof_of_eval_return_wit_19 : eval_return_wit_19.
Axiom proof_of_eval_return_wit_20 : eval_return_wit_20.
Axiom proof_of_eval_return_wit_21 : eval_return_wit_21.
Axiom proof_of_eval_return_wit_22 : eval_return_wit_22.
Axiom proof_of_eval_return_wit_23 : eval_return_wit_23.
Axiom proof_of_eval_return_wit_24 : eval_return_wit_24.
Axiom proof_of_eval_return_wit_25 : eval_return_wit_25.
Axiom proof_of_eval_return_wit_26 : eval_return_wit_26.
Axiom proof_of_eval_return_wit_27 : eval_return_wit_27.
Axiom proof_of_eval_return_wit_28 : eval_return_wit_28.
Axiom proof_of_eval_partial_solve_wit_1 : eval_partial_solve_wit_1.
Axiom proof_of_eval_partial_solve_wit_2_pure : eval_partial_solve_wit_2_pure.
Axiom proof_of_eval_partial_solve_wit_2 : eval_partial_solve_wit_2.
Axiom proof_of_eval_partial_solve_wit_3_pure : eval_partial_solve_wit_3_pure.
Axiom proof_of_eval_partial_solve_wit_3 : eval_partial_solve_wit_3.
Axiom proof_of_eval_partial_solve_wit_4 : eval_partial_solve_wit_4.
Axiom proof_of_eval_partial_solve_wit_5_pure : eval_partial_solve_wit_5_pure.
Axiom proof_of_eval_partial_solve_wit_5 : eval_partial_solve_wit_5.
Axiom proof_of_eval_partial_solve_wit_6_pure : eval_partial_solve_wit_6_pure.
Axiom proof_of_eval_partial_solve_wit_6 : eval_partial_solve_wit_6.
Axiom proof_of_eval_partial_solve_wit_7_pure : eval_partial_solve_wit_7_pure.
Axiom proof_of_eval_partial_solve_wit_7 : eval_partial_solve_wit_7.
Axiom proof_of_eval_partial_solve_wit_8_pure : eval_partial_solve_wit_8_pure.
Axiom proof_of_eval_partial_solve_wit_8 : eval_partial_solve_wit_8.
Axiom proof_of_eval_partial_solve_wit_9_pure : eval_partial_solve_wit_9_pure.
Axiom proof_of_eval_partial_solve_wit_9 : eval_partial_solve_wit_9.
Axiom proof_of_eval_partial_solve_wit_10_pure : eval_partial_solve_wit_10_pure.
Axiom proof_of_eval_partial_solve_wit_10 : eval_partial_solve_wit_10.
Axiom proof_of_eval_partial_solve_wit_11_pure : eval_partial_solve_wit_11_pure.
Axiom proof_of_eval_partial_solve_wit_11 : eval_partial_solve_wit_11.
Axiom proof_of_eval_partial_solve_wit_12_pure : eval_partial_solve_wit_12_pure.
Axiom proof_of_eval_partial_solve_wit_12 : eval_partial_solve_wit_12.
Axiom proof_of_eval_partial_solve_wit_13_pure : eval_partial_solve_wit_13_pure.
Axiom proof_of_eval_partial_solve_wit_13 : eval_partial_solve_wit_13.
Axiom proof_of_eval_partial_solve_wit_14_pure : eval_partial_solve_wit_14_pure.
Axiom proof_of_eval_partial_solve_wit_14 : eval_partial_solve_wit_14.
Axiom proof_of_eval_which_implies_wit_1 : eval_which_implies_wit_1.
Axiom proof_of_eval_which_implies_wit_2 : eval_which_implies_wit_2.
Axiom proof_of_eval_which_implies_wit_3 : eval_which_implies_wit_3.
Axiom proof_of_eval_which_implies_wit_4 : eval_which_implies_wit_4.
Axiom proof_of_eval_which_implies_wit_5 : eval_which_implies_wit_5.

End VC_Correct.
