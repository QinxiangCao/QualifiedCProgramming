Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope R_scope.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

(*----- Function float_identity -----*)

Definition float_identity_return_wit_1 := 
forall (x_pre: fp32) ,
  TT && emp 
|--
  “ (fp32_eq x_pre x_pre) ”
  &&  emp
.

(*----- Function float_one_from_int -----*)

Definition float_one_from_int_safety_wit_1 := 
  TT && emp 
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition float_one_from_int_return_wit_1 := 
  TT && emp 
|--
  “ (fp32_eq (Z_to_fp32 (1)) (fp32_of_real (1.0))) ”
  &&  emp
.

(*----- Function int_to_float -----*)

Definition int_to_float_return_wit_1 := 
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (x_pre <= 16777216)) ,
  TT && emp 
|--
  “ (fp32_eq (Z_to_fp32 (x_pre)) (Z_to_fp32 (x_pre))) ”
  &&  emp
.

(*----- Function float_one -----*)

Definition float_one_return_wit_1 := 
  TT && emp 
|--
  “ (fp32_eq (fp32_of_real (1.0)) (fp32_of_real (1.0))) ”
  &&  emp
.

(*----- Function double_identity -----*)

Definition double_identity_return_wit_1 := 
forall (x_pre: fp64) ,
  TT && emp 
|--
  “ (fp64_eq x_pre x_pre) ”
  &&  emp
.

(*----- Function float_literals -----*)

Definition float_literals_return_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

(*----- Function double_literals -----*)

Definition double_literals_return_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

(*----- Function float_literal_addition -----*)

Definition float_literal_addition_return_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

(*----- Function double_literal_addition -----*)

Definition double_literal_addition_return_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

(*----- Function float_add_literal -----*)

Definition float_add_literal_return_wit_1 := 
forall (x_pre: fp32) (PreH1 : (fp32_isFinite x_pre )) (PreH2 : (fp32_lt x_pre (fp32_sub FLT_MAX (fp32_of_real (1.0))))) ,
  TT && emp 
|--
  “ (fp32_eq (fp32_add (x_pre) ((fp32_of_real (1.0)))) (fp32_add (x_pre) ((fp32_of_real (1.0))))) ”
  &&  emp
.

(*----- Function float_add_int_literal -----*)

Definition float_add_int_literal_safety_wit_1 := 
forall (x_pre: fp32) (PreH1 : (fp32_isFinite x_pre )) (PreH2 : (fp32_lt x_pre (fp32_sub FLT_MAX (fp32_of_real (1.0))))) ,
  ((( &( "x" ) )) # Float  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition float_add_int_literal_return_wit_1 := 
forall (x_pre: fp32) (PreH1 : (fp32_isFinite x_pre )) (PreH2 : (fp32_lt x_pre (fp32_sub FLT_MAX (fp32_of_real (1.0))))) ,
  TT && emp 
|--
  “ (fp32_eq (fp32_add (x_pre) ((Z_to_fp32 (1)))) (fp32_add (x_pre) ((fp32_of_real (1.0))))) ”
  &&  emp
.

(*----- Function double_add_literal -----*)

Definition double_add_literal_return_wit_1 := 
forall (x_pre: fp64) (PreH1 : (fp64_isFinite x_pre )) (PreH2 : (fp64_lt x_pre (fp64_sub DBL_MAX (fp64_of_real (1.0))))) ,
  TT && emp 
|--
  “ (fp64_eq (fp64_add (x_pre) ((fp64_of_real (1.0)))) (fp64_add (x_pre) ((fp64_of_real (1.0))))) ”
  &&  emp
.

(*----- Function float_literal_arithmetic -----*)

Definition float_literal_arithmetic_return_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

(*----- Function double_literal_arithmetic -----*)

Definition double_literal_arithmetic_return_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

(*----- Function float_neg -----*)

Definition float_neg_return_wit_1 := 
forall (x_pre: fp32) (PreH1 : (fp32_isFinite x_pre )) ,
  TT && emp 
|--
  “ (fp32_eq (fp32_neg (x_pre)) (fp32_neg (x_pre))) ”
  &&  emp
.

(*----- Function double_neg -----*)

Definition double_neg_return_wit_1 := 
forall (x_pre: fp64) (PreH1 : (fp64_isFinite x_pre )) ,
  TT && emp 
|--
  “ (fp64_eq (fp64_neg (x_pre)) (fp64_neg (x_pre))) ”
  &&  emp
.

(*----- Function float_sub -----*)

Definition float_sub_return_wit_1 := 
forall (y_pre: fp32) (x_pre: fp32) (PreH1 : (fp32_isFinite x_pre )) (PreH2 : (fp32_isFinite y_pre )) (PreH3 : (fp32_isFinite (fp32_sub (x_pre) (y_pre)) )) ,
  TT && emp 
|--
  “ (fp32_eq (fp32_sub (x_pre) (y_pre)) (fp32_sub (x_pre) (y_pre))) ”
  &&  emp
.

(*----- Function double_sub -----*)

Definition double_sub_return_wit_1 := 
forall (y_pre: fp64) (x_pre: fp64) (PreH1 : (fp64_isFinite x_pre )) (PreH2 : (fp64_isFinite y_pre )) (PreH3 : (fp64_isFinite (fp64_sub (x_pre) (y_pre)) )) ,
  TT && emp 
|--
  “ (fp64_eq (fp64_sub (x_pre) (y_pre)) (fp64_sub (x_pre) (y_pre))) ”
  &&  emp
.

(*----- Function float_mul -----*)

Definition float_mul_return_wit_1 := 
forall (y_pre: fp32) (x_pre: fp32) (PreH1 : (fp32_isFinite x_pre )) (PreH2 : (fp32_isFinite y_pre )) (PreH3 : (fp32_isFinite (fp32_mul (x_pre) (y_pre)) )) ,
  TT && emp 
|--
  “ (fp32_eq (fp32_mul (x_pre) (y_pre)) (fp32_mul (x_pre) (y_pre))) ”
  &&  emp
.

(*----- Function double_mul -----*)

Definition double_mul_return_wit_1 := 
forall (y_pre: fp64) (x_pre: fp64) (PreH1 : (fp64_isFinite x_pre )) (PreH2 : (fp64_isFinite y_pre )) (PreH3 : (fp64_isFinite (fp64_mul (x_pre) (y_pre)) )) ,
  TT && emp 
|--
  “ (fp64_eq (fp64_mul (x_pre) (y_pre)) (fp64_mul (x_pre) (y_pre))) ”
  &&  emp
.

(*----- Function float_div -----*)

Definition float_div_return_wit_1 := 
forall (y_pre: fp32) (x_pre: fp32) (PreH1 : (fp32_isFinite x_pre )) (PreH2 : (fp32_isFinite y_pre )) (PreH3 : (fp32_ne y_pre (fp32_of_real (0.0)) )) (PreH4 : (fp32_isFinite (fp32_div (x_pre) (y_pre)) )) ,
  TT && emp 
|--
  “ (fp32_eq (fp32_div (x_pre) (y_pre)) (fp32_div (x_pre) (y_pre))) ”
  &&  emp
.

(*----- Function double_div -----*)

Definition double_div_return_wit_1 := 
forall (y_pre: fp64) (x_pre: fp64) (PreH1 : (fp64_isFinite x_pre )) (PreH2 : (fp64_isFinite y_pre )) (PreH3 : (fp64_ne y_pre (fp64_of_real (0.0)) )) (PreH4 : (fp64_isFinite (fp64_div (x_pre) (y_pre)) )) ,
  TT && emp 
|--
  “ (fp64_eq (fp64_div (x_pre) (y_pre)) (fp64_div (x_pre) (y_pre))) ”
  &&  emp
.

(*----- Function float_mixed_expression -----*)

Definition float_mixed_expression_return_wit_1 := 
forall (y_pre: fp32) (x_pre: fp32) (PreH1 : (fp32_isFinite x_pre )) (PreH2 : (fp32_isFinite y_pre )) (PreH3 : (fp32_isFinite (fp32_mul ((fp32_add (x_pre) (y_pre))) ((fp32_sub (x_pre) (y_pre)))) )) ,
  TT && emp 
|--
  “ (fp32_eq (fp32_mul ((fp32_add (x_pre) (y_pre))) ((fp32_sub (x_pre) (y_pre)))) (fp32_mul ((fp32_add (x_pre) (y_pre))) ((fp32_sub (x_pre) (y_pre))))) ”
  &&  emp
.

(*----- Function double_mixed_expression -----*)

Definition double_mixed_expression_return_wit_1 := 
forall (y_pre: fp64) (x_pre: fp64) (PreH1 : (fp64_isFinite x_pre )) (PreH2 : (fp64_isFinite y_pre )) (PreH3 : (fp64_isFinite (fp64_add (x_pre) (y_pre)) )) (PreH4 : (fp64_isFinite (fp64_sub (x_pre) (y_pre)) )) (PreH5 : (fp64_isFinite (fp64_mul ((fp64_add (x_pre) (y_pre))) ((fp64_sub (x_pre) (y_pre)))) )) ,
  TT && emp 
|--
  “ (fp64_eq (fp64_mul ((fp64_add (x_pre) (y_pre))) ((fp64_sub (x_pre) (y_pre)))) (fp64_mul ((fp64_add (x_pre) (y_pre))) ((fp64_sub (x_pre) (y_pre))))) ”
  &&  emp
.

(*----- Function float_add_sub_chain -----*)

Definition float_add_sub_chain_return_wit_1 := 
forall (z_pre: fp32) (y_pre: fp32) (x_pre: fp32) (PreH1 : (fp32_isFinite x_pre )) (PreH2 : (fp32_isFinite y_pre )) (PreH3 : (fp32_isFinite z_pre )) (PreH4 : (fp32_isFinite (fp32_add (x_pre) (y_pre)) )) (PreH5 : (fp32_isFinite (fp32_sub ((fp32_add (x_pre) (y_pre))) (z_pre)) )) ,
  TT && emp 
|--
  “ (fp32_eq (fp32_sub ((fp32_add (x_pre) (y_pre))) (z_pre)) (fp32_sub ((fp32_add (x_pre) (y_pre))) (z_pre))) ”
  &&  emp
.

(*----- Function double_mul_add_chain -----*)

Definition double_mul_add_chain_return_wit_1 := 
forall (z_pre: fp64) (y_pre: fp64) (x_pre: fp64) (PreH1 : (fp64_isFinite x_pre )) (PreH2 : (fp64_isFinite y_pre )) (PreH3 : (fp64_isFinite z_pre )) (PreH4 : (fp64_isFinite (fp64_mul (x_pre) (y_pre)) )) (PreH5 : (fp64_isFinite (fp64_add ((fp64_mul (x_pre) (y_pre))) (z_pre)) )) ,
  TT && emp 
|--
  “ (fp64_eq (fp64_add ((fp64_mul (x_pre) (y_pre))) (z_pre)) (fp64_add ((fp64_mul (x_pre) (y_pre))) (z_pre))) ”
  &&  emp
.

(*----- Function float_literal_mul_exact -----*)

Definition float_literal_mul_exact_return_wit_1 := 
  TT && emp 
|--
  “ (fp32_eq (fp32_mul ((fp32_of_real (1.5))) ((fp32_of_real (2.0)))) (fp32_of_real (3.0))) ”
  &&  emp
.

(*----- Function double_literal_div_exact -----*)

Definition double_literal_div_exact_return_wit_1 := 
  TT && emp 
|--
  “ (fp64_eq (fp64_div ((fp64_of_real (7.5))) ((fp64_of_real (2.5)))) (fp64_of_real (3.0))) ”
  &&  emp
.

(*----- Function float_sub_self_zero_branch -----*)

Definition float_sub_self_zero_branch_safety_wit_1 := 
forall (x_pre: fp32) (PreH1 : (fp32_ne (fp32_sub (x_pre) (x_pre)) (fp32_of_real (0.0)) )) (PreH2 : (fp32_isFinite x_pre )) (PreH3 : (fp32_isFinite (fp32_sub (x_pre) (x_pre)) )) ,
  ((( &( "x" ) )) # Float  |-> x_pre)
|--
  “ False ”
.

Definition float_sub_self_zero_branch_safety_wit_2 := 
forall (x_pre: fp32) (PreH1 : (fp32_eq (fp32_sub (x_pre) (x_pre)) (fp32_of_real (0.0)) )) (PreH2 : (fp32_isFinite x_pre )) (PreH3 : (fp32_isFinite (fp32_sub (x_pre) (x_pre)) )) ,
  ((( &( "x" ) )) # Float  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition float_sub_self_zero_branch_return_wit_1 := 
forall (x_pre: fp32) (PreH1 : (fp32_eq (fp32_sub (x_pre) (x_pre)) (fp32_of_real (0.0)) )) (PreH2 : (fp32_isFinite x_pre )) (PreH3 : (fp32_isFinite (fp32_sub (x_pre) (x_pre)) )) ,
  TT && emp 
|--
  “ (1 = 1) ”
  &&  emp
.

(*----- Function double_div_self_one_branch -----*)

Definition double_div_self_one_branch_safety_wit_1 := 
forall (x_pre: fp64) (PreH1 : (fp64_ne (fp64_div (x_pre) (x_pre)) (fp64_of_real (1.0)) )) (PreH2 : (fp64_isFinite x_pre )) (PreH3 : (fp64_ne x_pre (fp64_of_real (0.0)) )) (PreH4 : (fp64_isFinite (fp64_div (x_pre) (x_pre)) )) ,
  ((( &( "x" ) )) # Double  |-> x_pre)
|--
  “ False ”
.

Definition double_div_self_one_branch_safety_wit_2 := 
forall (x_pre: fp64) (PreH1 : (fp64_eq (fp64_div (x_pre) (x_pre)) (fp64_of_real (1.0)) )) (PreH2 : (fp64_isFinite x_pre )) (PreH3 : (fp64_ne x_pre (fp64_of_real (0.0)) )) (PreH4 : (fp64_isFinite (fp64_div (x_pre) (x_pre)) )) ,
  ((( &( "x" ) )) # Double  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition double_div_self_one_branch_return_wit_1 := 
forall (x_pre: fp64) (PreH1 : (fp64_eq (fp64_div (x_pre) (x_pre)) (fp64_of_real (1.0)) )) (PreH2 : (fp64_isFinite x_pre )) (PreH3 : (fp64_ne x_pre (fp64_of_real (0.0)) )) (PreH4 : (fp64_isFinite (fp64_div (x_pre) (x_pre)) )) ,
  TT && emp 
|--
  “ (1 = 1) ”
  &&  emp
.

(*----- Function float_neg_involution_branch -----*)

Definition float_neg_involution_branch_safety_wit_1 := 
forall (x_pre: fp32) (PreH1 : (fp32_ne (fp32_neg ((fp32_neg (x_pre)))) x_pre )) (PreH2 : (fp32_isFinite x_pre )) (PreH3 : (fp32_isFinite (fp32_neg (x_pre)) )) (PreH4 : (fp32_isFinite (fp32_neg ((fp32_neg (x_pre)))) )) ,
  ((( &( "x" ) )) # Float  |-> x_pre)
|--
  “ False ”
.

Definition float_neg_involution_branch_safety_wit_2 := 
forall (x_pre: fp32) (PreH1 : (fp32_eq (fp32_neg ((fp32_neg (x_pre)))) x_pre )) (PreH2 : (fp32_isFinite x_pre )) (PreH3 : (fp32_isFinite (fp32_neg (x_pre)) )) (PreH4 : (fp32_isFinite (fp32_neg ((fp32_neg (x_pre)))) )) ,
  ((( &( "x" ) )) # Float  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition float_neg_involution_branch_return_wit_1 := 
forall (x_pre: fp32) (PreH1 : (fp32_eq (fp32_neg ((fp32_neg (x_pre)))) x_pre )) (PreH2 : (fp32_isFinite x_pre )) (PreH3 : (fp32_isFinite (fp32_neg (x_pre)) )) (PreH4 : (fp32_isFinite (fp32_neg ((fp32_neg (x_pre)))) )) ,
  TT && emp 
|--
  “ (1 = 1) ”
  &&  emp
.

(*----- Function float_lt_branch -----*)

Definition float_lt_branch_safety_wit_1 := 
forall (y_pre: fp32) (x_pre: fp32) (PreH1 : (fp32_lt x_pre y_pre )) (PreH2 : (fp32_isFinite x_pre )) (PreH3 : (fp32_isFinite y_pre )) ,
  ((( &( "y" ) )) # Float  |-> y_pre)
  **  ((( &( "x" ) )) # Float  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition float_lt_branch_safety_wit_2 := 
forall (y_pre: fp32) (x_pre: fp32) (PreH1 : (fp32_ge x_pre y_pre )) (PreH2 : (fp32_isFinite x_pre )) (PreH3 : (fp32_isFinite y_pre )) ,
  ((( &( "y" ) )) # Float  |-> y_pre)
  **  ((( &( "x" ) )) # Float  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition float_lt_branch_return_wit_1 := 
forall (y_pre: fp32) (x_pre: fp32) (PreH1 : (fp32_ge x_pre y_pre )) (PreH2 : (fp32_isFinite x_pre )) (PreH3 : (fp32_isFinite y_pre )) ,
  TT && emp 
|--
  “ (fp32_ge x_pre y_pre ) ” 
  &&  “ (0 = 0) ”
  &&  emp
.

Definition float_lt_branch_return_wit_2 := 
forall (y_pre: fp32) (x_pre: fp32) (PreH1 : (fp32_lt x_pre y_pre )) (PreH2 : (fp32_isFinite x_pre )) (PreH3 : (fp32_isFinite y_pre )) ,
  TT && emp 
|--
  “ (fp32_lt x_pre y_pre ) ” 
  &&  “ (1 = 1) ”
  &&  emp
.

(*----- Function float_ne_branch -----*)

Definition float_ne_branch_safety_wit_1 := 
forall (y_pre: fp32) (x_pre: fp32) (PreH1 : (fp32_ne x_pre y_pre )) (PreH2 : (fp32_isFinite x_pre )) (PreH3 : (fp32_isFinite y_pre )) ,
  ((( &( "y" ) )) # Float  |-> y_pre)
  **  ((( &( "x" ) )) # Float  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition float_ne_branch_safety_wit_2 := 
forall (y_pre: fp32) (x_pre: fp32) (PreH1 : (fp32_eq x_pre y_pre )) (PreH2 : (fp32_isFinite x_pre )) (PreH3 : (fp32_isFinite y_pre )) ,
  ((( &( "y" ) )) # Float  |-> y_pre)
  **  ((( &( "x" ) )) # Float  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition float_ne_branch_return_wit_1 := 
forall (y_pre: fp32) (x_pre: fp32) (PreH1 : (fp32_eq x_pre y_pre )) (PreH2 : (fp32_isFinite x_pre )) (PreH3 : (fp32_isFinite y_pre )) ,
  TT && emp 
|--
  “ (fp32_eq x_pre y_pre ) ” 
  &&  “ (0 = 0) ”
  &&  emp
.

Definition float_ne_branch_return_wit_2 := 
forall (y_pre: fp32) (x_pre: fp32) (PreH1 : (fp32_ne x_pre y_pre )) (PreH2 : (fp32_isFinite x_pre )) (PreH3 : (fp32_isFinite y_pre )) ,
  TT && emp 
|--
  “ (fp32_ne x_pre y_pre ) ” 
  &&  “ (1 = 1) ”
  &&  emp
.

(*----- Function double_eq_branch -----*)

Definition double_eq_branch_safety_wit_1 := 
forall (y_pre: fp64) (x_pre: fp64) (PreH1 : (fp64_eq x_pre y_pre )) (PreH2 : (fp64_isFinite x_pre )) (PreH3 : (fp64_isFinite y_pre )) ,
  ((( &( "y" ) )) # Double  |-> y_pre)
  **  ((( &( "x" ) )) # Double  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition double_eq_branch_safety_wit_2 := 
forall (y_pre: fp64) (x_pre: fp64) (PreH1 : (fp64_ne x_pre y_pre )) (PreH2 : (fp64_isFinite x_pre )) (PreH3 : (fp64_isFinite y_pre )) ,
  ((( &( "y" ) )) # Double  |-> y_pre)
  **  ((( &( "x" ) )) # Double  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition double_eq_branch_return_wit_1 := 
forall (y_pre: fp64) (x_pre: fp64) (PreH1 : (fp64_ne x_pre y_pre )) (PreH2 : (fp64_isFinite x_pre )) (PreH3 : (fp64_isFinite y_pre )) ,
  TT && emp 
|--
  “ (fp64_ne x_pre y_pre ) ” 
  &&  “ (0 = 0) ”
  &&  emp
.

Definition double_eq_branch_return_wit_2 := 
forall (y_pre: fp64) (x_pre: fp64) (PreH1 : (fp64_eq x_pre y_pre )) (PreH2 : (fp64_isFinite x_pre )) (PreH3 : (fp64_isFinite y_pre )) ,
  TT && emp 
|--
  “ (fp64_eq x_pre y_pre ) ” 
  &&  “ (1 = 1) ”
  &&  emp
.

(*----- Function double_ge_branch -----*)

Definition double_ge_branch_safety_wit_1 := 
forall (y_pre: fp64) (x_pre: fp64) (PreH1 : (fp64_ge x_pre y_pre )) (PreH2 : (fp64_isFinite x_pre )) (PreH3 : (fp64_isFinite y_pre )) ,
  ((( &( "y" ) )) # Double  |-> y_pre)
  **  ((( &( "x" ) )) # Double  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition double_ge_branch_safety_wit_2 := 
forall (y_pre: fp64) (x_pre: fp64) (PreH1 : (fp64_lt x_pre y_pre )) (PreH2 : (fp64_isFinite x_pre )) (PreH3 : (fp64_isFinite y_pre )) ,
  ((( &( "y" ) )) # Double  |-> y_pre)
  **  ((( &( "x" ) )) # Double  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition double_ge_branch_return_wit_1 := 
forall (y_pre: fp64) (x_pre: fp64) (PreH1 : (fp64_lt x_pre y_pre )) (PreH2 : (fp64_isFinite x_pre )) (PreH3 : (fp64_isFinite y_pre )) ,
  TT && emp 
|--
  “ (fp64_lt x_pre y_pre ) ” 
  &&  “ (0 = 0) ”
  &&  emp
.

Definition double_ge_branch_return_wit_2 := 
forall (y_pre: fp64) (x_pre: fp64) (PreH1 : (fp64_ge x_pre y_pre )) (PreH2 : (fp64_isFinite x_pre )) (PreH3 : (fp64_isFinite y_pre )) ,
  TT && emp 
|--
  “ (fp64_ge x_pre y_pre ) ” 
  &&  “ (1 = 1) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_float_identity_return_wit_1 : float_identity_return_wit_1.
Axiom proof_of_float_one_from_int_safety_wit_1 : float_one_from_int_safety_wit_1.
Axiom proof_of_float_one_from_int_return_wit_1 : float_one_from_int_return_wit_1.
Axiom proof_of_int_to_float_return_wit_1 : int_to_float_return_wit_1.
Axiom proof_of_float_one_return_wit_1 : float_one_return_wit_1.
Axiom proof_of_double_identity_return_wit_1 : double_identity_return_wit_1.
Axiom proof_of_float_literals_return_wit_1 : float_literals_return_wit_1.
Axiom proof_of_double_literals_return_wit_1 : double_literals_return_wit_1.
Axiom proof_of_float_literal_addition_return_wit_1 : float_literal_addition_return_wit_1.
Axiom proof_of_double_literal_addition_return_wit_1 : double_literal_addition_return_wit_1.
Axiom proof_of_float_add_literal_return_wit_1 : float_add_literal_return_wit_1.
Axiom proof_of_float_add_int_literal_safety_wit_1 : float_add_int_literal_safety_wit_1.
Axiom proof_of_float_add_int_literal_return_wit_1 : float_add_int_literal_return_wit_1.
Axiom proof_of_double_add_literal_return_wit_1 : double_add_literal_return_wit_1.
Axiom proof_of_float_literal_arithmetic_return_wit_1 : float_literal_arithmetic_return_wit_1.
Axiom proof_of_double_literal_arithmetic_return_wit_1 : double_literal_arithmetic_return_wit_1.
Axiom proof_of_float_neg_return_wit_1 : float_neg_return_wit_1.
Axiom proof_of_double_neg_return_wit_1 : double_neg_return_wit_1.
Axiom proof_of_float_sub_return_wit_1 : float_sub_return_wit_1.
Axiom proof_of_double_sub_return_wit_1 : double_sub_return_wit_1.
Axiom proof_of_float_mul_return_wit_1 : float_mul_return_wit_1.
Axiom proof_of_double_mul_return_wit_1 : double_mul_return_wit_1.
Axiom proof_of_float_div_return_wit_1 : float_div_return_wit_1.
Axiom proof_of_double_div_return_wit_1 : double_div_return_wit_1.
Axiom proof_of_float_mixed_expression_return_wit_1 : float_mixed_expression_return_wit_1.
Axiom proof_of_double_mixed_expression_return_wit_1 : double_mixed_expression_return_wit_1.
Axiom proof_of_float_add_sub_chain_return_wit_1 : float_add_sub_chain_return_wit_1.
Axiom proof_of_double_mul_add_chain_return_wit_1 : double_mul_add_chain_return_wit_1.
Axiom proof_of_float_literal_mul_exact_return_wit_1 : float_literal_mul_exact_return_wit_1.
Axiom proof_of_double_literal_div_exact_return_wit_1 : double_literal_div_exact_return_wit_1.
Axiom proof_of_float_sub_self_zero_branch_safety_wit_1 : float_sub_self_zero_branch_safety_wit_1.
Axiom proof_of_float_sub_self_zero_branch_safety_wit_2 : float_sub_self_zero_branch_safety_wit_2.
Axiom proof_of_float_sub_self_zero_branch_return_wit_1 : float_sub_self_zero_branch_return_wit_1.
Axiom proof_of_double_div_self_one_branch_safety_wit_1 : double_div_self_one_branch_safety_wit_1.
Axiom proof_of_double_div_self_one_branch_safety_wit_2 : double_div_self_one_branch_safety_wit_2.
Axiom proof_of_double_div_self_one_branch_return_wit_1 : double_div_self_one_branch_return_wit_1.
Axiom proof_of_float_neg_involution_branch_safety_wit_1 : float_neg_involution_branch_safety_wit_1.
Axiom proof_of_float_neg_involution_branch_safety_wit_2 : float_neg_involution_branch_safety_wit_2.
Axiom proof_of_float_neg_involution_branch_return_wit_1 : float_neg_involution_branch_return_wit_1.
Axiom proof_of_float_lt_branch_safety_wit_1 : float_lt_branch_safety_wit_1.
Axiom proof_of_float_lt_branch_safety_wit_2 : float_lt_branch_safety_wit_2.
Axiom proof_of_float_lt_branch_return_wit_1 : float_lt_branch_return_wit_1.
Axiom proof_of_float_lt_branch_return_wit_2 : float_lt_branch_return_wit_2.
Axiom proof_of_float_ne_branch_safety_wit_1 : float_ne_branch_safety_wit_1.
Axiom proof_of_float_ne_branch_safety_wit_2 : float_ne_branch_safety_wit_2.
Axiom proof_of_float_ne_branch_return_wit_1 : float_ne_branch_return_wit_1.
Axiom proof_of_float_ne_branch_return_wit_2 : float_ne_branch_return_wit_2.
Axiom proof_of_double_eq_branch_safety_wit_1 : double_eq_branch_safety_wit_1.
Axiom proof_of_double_eq_branch_safety_wit_2 : double_eq_branch_safety_wit_2.
Axiom proof_of_double_eq_branch_return_wit_1 : double_eq_branch_return_wit_1.
Axiom proof_of_double_eq_branch_return_wit_2 : double_eq_branch_return_wit_2.
Axiom proof_of_double_ge_branch_safety_wit_1 : double_ge_branch_safety_wit_1.
Axiom proof_of_double_ge_branch_safety_wit_2 : double_ge_branch_safety_wit_2.
Axiom proof_of_double_ge_branch_return_wit_1 : double_ge_branch_return_wit_1.
Axiom proof_of_double_ge_branch_return_wit_2 : double_ge_branch_return_wit_2.

End VC_Correct.
