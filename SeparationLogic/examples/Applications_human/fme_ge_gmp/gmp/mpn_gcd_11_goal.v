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
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_proof.

(*----- Function gmp_ctz -----*)

Definition gmp_ctz_safety_wit_1 := 
forall (x_pre: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 32)) (PreH3 : ((Z.pow (2) (31)) <= ((Z.land x_pre (-x_pre)) * (Z.pow (2) (retval)) ))) (PreH4 : (((Z.land x_pre (-x_pre)) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH5 : (0 < x_pre)) (PreH6 : (x_pre <= UINT_MAX)) ,
  ((( &( "__ctz_c" ) )) # UInt  |-> retval)
  **  ((( &( "__ctz_x" ) )) # UInt  |-> x_pre)
  **  ((( &( "x" ) )) # UInt  |-> x_pre)
|--
  “ (31 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 31) ”
.

Definition gmp_ctz_return_wit_1 := 
(
forall (x_pre: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 32)) (PreH3 : ((Z.pow (2) (31)) <= ((Z.land x_pre (-x_pre)) * (Z.pow (2) (retval)) ))) (PreH4 : (((Z.land x_pre (-x_pre)) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH5 : (0 < x_pre)) (PreH6 : (x_pre <= UINT_MAX)) ,
  TT && emp 
|--
  EX (odd: Z) ,
  “ (0 <= (31 - retval )) ” 
  &&  “ ((31 - retval ) < 32) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ (x_pre = (odd * (Z.pow (2) ((31 - retval ))) )) ”
  &&  emp
) \/
(
forall (x_pre: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 32)) (PreH3 : ((Z.pow (2) (31)) <= ((Z.land x_pre (-x_pre)) * (Z.pow (2) (retval)) ))) (PreH4 : (((Z.land x_pre (-x_pre)) * (Z.pow (2) (retval)) ) < (Z.pow (2) (32)))) (PreH5 : (0 < x_pre)) (PreH6 : (x_pre <= UINT_MAX)) ,
  TT && emp 
|--
  EX (odd: Z) ,
  “ (0 <= (31 - retval )) ” 
  &&  “ ((31 - retval ) < 32) ” 
  &&  “ (odd > 0) ” 
  &&  “ ((odd % ( 2 ) ) = 1) ” 
  &&  “ (x_pre = (odd * (Z.pow (2) ((31 - retval ))) )) ”
  &&  emp
).

Definition gmp_ctz_partial_solve_wit_1_pure := 
(
forall (x_pre: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= UINT_MAX)) ,
  ((( &( "__ctz_c" ) )) # UInt  |->_)
  **  ((( &( "__ctz_x" ) )) # UInt  |-> x_pre)
  **  ((( &( "x" ) )) # UInt  |-> x_pre)
|--
  “ ((Z.land x_pre (-x_pre)) <= UINT_MAX) ” 
  &&  “ (0 < (Z.land x_pre (-x_pre))) ”
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= UINT_MAX)) ,
  ((( &( "__ctz_c" ) )) # UInt  |->_)
  **  ((( &( "__ctz_x" ) )) # UInt  |-> x_pre)
  **  ((( &( "x" ) )) # UInt  |-> x_pre)
|--
  “ (0 < (Z.land x_pre (-x_pre))) ” 
  &&  “ ((Z.land x_pre (-x_pre)) <= UINT_MAX) ”
).

Definition gmp_ctz_partial_solve_wit_1_pure_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= UINT_MAX)) ,
  ((( &( "__ctz_c" ) )) # UInt  |->_)
  **  ((( &( "__ctz_x" ) )) # UInt  |-> x_pre)
  **  ((( &( "x" ) )) # UInt  |-> x_pre)
|--
  “ (0 < (Z.land x_pre (-x_pre))) ”
.

Definition gmp_ctz_partial_solve_wit_1_pure_split_goal_2 := 
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= UINT_MAX)) ,
  ((( &( "__ctz_c" ) )) # UInt  |->_)
  **  ((( &( "__ctz_x" ) )) # UInt  |-> x_pre)
  **  ((( &( "x" ) )) # UInt  |-> x_pre)
|--
  “ ((Z.land x_pre (-x_pre)) <= UINT_MAX) ”
.

Definition gmp_ctz_partial_solve_wit_1_aux := 
forall (x_pre: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= UINT_MAX)) ,
  TT && emp 
|--
  “ ((Z.land x_pre (-x_pre)) <= UINT_MAX) ” 
  &&  “ (0 < (Z.land x_pre (-x_pre))) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (x_pre <= UINT_MAX) ”
  &&  emp
.

Definition gmp_ctz_partial_solve_wit_1 := gmp_ctz_partial_solve_wit_1_pure -> gmp_ctz_partial_solve_wit_1_aux.

(*----- Function mpn_gcd_11 -----*)

Definition mpn_gcd_11_safety_wit_1 := 
forall (v_pre: Z) (u_pre: Z) (PreH1 : (0 <= u_pre)) (PreH2 : (u_pre <= UINT_MAX)) (PreH3 : (0 <= v_pre)) (PreH4 : (v_pre <= UINT_MAX)) (PreH5 : ((u_pre + v_pre ) > 0)) ,
  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "v" ) )) # UInt  |-> v_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_gcd_11_safety_wit_2 := 
forall (v_pre: Z) (u_pre: Z) (PreH1 : (u_pre <> 0)) (PreH2 : (0 <= u_pre)) (PreH3 : (u_pre <= UINT_MAX)) (PreH4 : (0 <= v_pre)) (PreH5 : (v_pre <= UINT_MAX)) (PreH6 : ((u_pre + v_pre ) > 0)) ,
  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "v" ) )) # UInt  |-> v_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_gcd_11_safety_wit_3 := 
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 32)) (PreH3 : (odd > 0)) (PreH4 : ((odd % ( 2 ) ) = 1)) (PreH5 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH6 : (v_pre <> 0)) (PreH7 : (u_pre <> 0)) (PreH8 : (0 <= u_pre)) (PreH9 : (u_pre <= UINT_MAX)) (PreH10 : (0 <= v_pre)) (PreH11 : (v_pre <= UINT_MAX)) (PreH12 : ((u_pre + v_pre ) > 0)) ,
  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "v" ) )) # UInt  |-> v_pre)
|--
  “ (retval <= 31) ” 
  &&  “ (0 <= retval) ”
.

Definition mpn_gcd_11_safety_wit_4 := 
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 32)) (PreH3 : (odd > 0)) (PreH4 : ((odd % ( 2 ) ) = 1)) (PreH5 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH6 : (v_pre <> 0)) (PreH7 : (u_pre <> 0)) (PreH8 : (0 <= u_pre)) (PreH9 : (u_pre <= UINT_MAX)) (PreH10 : (0 <= v_pre)) (PreH11 : (v_pre <= UINT_MAX)) (PreH12 : ((u_pre + v_pre ) > 0)) ,
  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "u" ) )) # UInt  |-> (Z.shiftr u_pre retval))
  **  ((( &( "v" ) )) # UInt  |-> v_pre)
|--
  “ (retval <= 31) ” 
  &&  “ (0 <= retval) ”
.

Definition mpn_gcd_11_safety_wit_5 := 
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 32)) (PreH3 : (odd > 0)) (PreH4 : ((odd % ( 2 ) ) = 1)) (PreH5 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH6 : (v_pre <> 0)) (PreH7 : (u_pre <> 0)) (PreH8 : (0 <= u_pre)) (PreH9 : (u_pre <= UINT_MAX)) (PreH10 : (0 <= v_pre)) (PreH11 : (v_pre <= UINT_MAX)) (PreH12 : ((u_pre + v_pre ) > 0)) ,
  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "u" ) )) # UInt  |-> (Z.shiftr u_pre retval))
  **  ((( &( "v" ) )) # UInt  |-> (Z.shiftr v_pre retval))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_gcd_11_safety_wit_6 := 
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < 32)) (PreH3 : (odd > 0)) (PreH4 : ((odd % ( 2 ) ) = 1)) (PreH5 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH6 : (v_pre <> 0)) (PreH7 : (u_pre <> 0)) (PreH8 : (0 <= u_pre)) (PreH9 : (u_pre <= UINT_MAX)) (PreH10 : (0 <= v_pre)) (PreH11 : (v_pre <= UINT_MAX)) (PreH12 : ((u_pre + v_pre ) > 0)) ,
  ((( &( "shift" ) )) # UInt  |-> retval)
  **  ((( &( "u" ) )) # UInt  |-> (Z.shiftr u_pre retval))
  **  ((( &( "v" ) )) # UInt  |-> (Z.shiftr v_pre retval))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_gcd_11_safety_wit_7 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (0 <= shift)) (PreH2 : (shift < 32)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (0 <= v_pre)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (0 < u)) (PreH8 : (u <= UINT_MAX)) (PreH9 : (0 < v)) (PreH10 : (v <= UINT_MAX)) (PreH11 : ((Z.land u 1) <> 0)) (PreH12 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "u" ) )) # UInt  |-> u)
  **  ((( &( "v" ) )) # UInt  |-> v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_gcd_11_safety_wit_8 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (0 <= shift)) (PreH2 : (shift < 32)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (0 <= v_pre)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (0 < u)) (PreH8 : (u <= UINT_MAX)) (PreH9 : (0 < v)) (PreH10 : (v <= UINT_MAX)) (PreH11 : ((Z.land u 1) <> 0)) (PreH12 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "u" ) )) # UInt  |-> u)
  **  ((( &( "v" ) )) # UInt  |-> v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_gcd_11_safety_wit_9 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land v 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "u" ) )) # UInt  |-> u)
  **  ((( &( "v" ) )) # UInt  |-> v)
|--
  “ (1 <= 31) ” 
  &&  “ (0 <= 1) ”
.

Definition mpn_gcd_11_safety_wit_10 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land v 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "u" ) )) # UInt  |-> u)
  **  ((( &( "v" ) )) # UInt  |-> v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_gcd_11_safety_wit_11 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (u > v)) (PreH2 : (u <> v)) (PreH3 : (0 <= shift)) (PreH4 : (shift < 32)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= UINT_MAX)) (PreH9 : (0 < u)) (PreH10 : (u <= UINT_MAX)) (PreH11 : (0 < v)) (PreH12 : (v <= UINT_MAX)) (PreH13 : ((Z.land u 1) <> 0)) (PreH14 : ((Z.land v 1) <> 0)) (PreH15 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "u" ) )) # UInt  |-> (u - v ))
  **  ((( &( "v" ) )) # UInt  |-> v)
|--
  “ (1 <= 31) ” 
  &&  “ (0 <= 1) ”
.

Definition mpn_gcd_11_safety_wit_12 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (u > v)) (PreH2 : (u <> v)) (PreH3 : (0 <= shift)) (PreH4 : (shift < 32)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= UINT_MAX)) (PreH9 : (0 < u)) (PreH10 : (u <= UINT_MAX)) (PreH11 : (0 < v)) (PreH12 : (v <= UINT_MAX)) (PreH13 : ((Z.land u 1) <> 0)) (PreH14 : ((Z.land v 1) <> 0)) (PreH15 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "u" ) )) # UInt  |-> (u - v ))
  **  ((( &( "v" ) )) # UInt  |-> v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_gcd_11_safety_wit_13 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land u 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land v 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "u" ) )) # UInt  |-> u)
  **  ((( &( "v" ) )) # UInt  |-> v)
|--
  “ (1 <= 31) ” 
  &&  “ (0 <= 1) ”
.

Definition mpn_gcd_11_safety_wit_14 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land u 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land v 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "u" ) )) # UInt  |-> u)
  **  ((( &( "v" ) )) # UInt  |-> v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_gcd_11_safety_wit_15 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (0 <= shift)) (PreH2 : (shift < 32)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (0 <= v_pre)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (0 < u)) (PreH8 : (u <= UINT_MAX)) (PreH9 : (0 < v)) (PreH10 : (v <= UINT_MAX)) (PreH11 : ((Z.land v 1) <> 0)) (PreH12 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "u" ) )) # UInt  |-> u)
  **  ((( &( "v" ) )) # UInt  |-> v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_gcd_11_safety_wit_16 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (0 <= shift)) (PreH2 : (shift < 32)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (0 <= v_pre)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (0 < u)) (PreH8 : (u <= UINT_MAX)) (PreH9 : (0 < v)) (PreH10 : (v <= UINT_MAX)) (PreH11 : ((Z.land v 1) <> 0)) (PreH12 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "u" ) )) # UInt  |-> u)
  **  ((( &( "v" ) )) # UInt  |-> v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_gcd_11_safety_wit_17 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (u <= v)) (PreH2 : (u <> v)) (PreH3 : (0 <= shift)) (PreH4 : (shift < 32)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= UINT_MAX)) (PreH9 : (0 < u)) (PreH10 : (u <= UINT_MAX)) (PreH11 : (0 < v)) (PreH12 : (v <= UINT_MAX)) (PreH13 : ((Z.land u 1) <> 0)) (PreH14 : ((Z.land v 1) <> 0)) (PreH15 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "u" ) )) # UInt  |-> u)
  **  ((( &( "v" ) )) # UInt  |-> (v - u ))
|--
  “ (1 <= 31) ” 
  &&  “ (0 <= 1) ”
.

Definition mpn_gcd_11_safety_wit_18 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (u <= v)) (PreH2 : (u <> v)) (PreH3 : (0 <= shift)) (PreH4 : (shift < 32)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= UINT_MAX)) (PreH9 : (0 < u)) (PreH10 : (u <= UINT_MAX)) (PreH11 : (0 < v)) (PreH12 : (v <= UINT_MAX)) (PreH13 : ((Z.land u 1) <> 0)) (PreH14 : ((Z.land v 1) <> 0)) (PreH15 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "u" ) )) # UInt  |-> u)
  **  ((( &( "v" ) )) # UInt  |-> (v - u ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_gcd_11_safety_wit_19 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land v 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "u" ) )) # UInt  |-> u)
  **  ((( &( "v" ) )) # UInt  |-> v)
|--
  “ (1 <= 31) ” 
  &&  “ (0 <= 1) ”
.

Definition mpn_gcd_11_safety_wit_20 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land v 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "u" ) )) # UInt  |-> u)
  **  ((( &( "v" ) )) # UInt  |-> v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_gcd_11_safety_wit_21 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (0 <= shift)) (PreH2 : (shift < 32)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (0 <= v_pre)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (0 < u)) (PreH8 : (u <= UINT_MAX)) (PreH9 : (0 < v)) (PreH10 : (v <= UINT_MAX)) (PreH11 : ((Z.land u 1) <> 0)) (PreH12 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "u" ) )) # UInt  |-> u)
  **  ((( &( "v" ) )) # UInt  |-> v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_gcd_11_safety_wit_22 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (0 <= shift)) (PreH2 : (shift < 32)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (0 <= v_pre)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (0 < u)) (PreH8 : (u <= UINT_MAX)) (PreH9 : (0 < v)) (PreH10 : (v <= UINT_MAX)) (PreH11 : ((Z.land u 1) <> 0)) (PreH12 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "u" ) )) # UInt  |-> u)
  **  ((( &( "v" ) )) # UInt  |-> v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_gcd_11_safety_wit_23 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (u = v)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Z.land v 1) <> 0)) (PreH14 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "u" ) )) # UInt  |-> u)
  **  ((( &( "v" ) )) # UInt  |-> v)
|--
  “ (shift <= 31) ” 
  &&  “ (0 <= shift) ”
.

Definition mpn_gcd_11_entail_wit_1_1 := 
(
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : ((Z.land (Z.shiftr u_pre retval) 1) = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH7 : (v_pre <> 0)) (PreH8 : (u_pre <> 0)) (PreH9 : (0 <= u_pre)) (PreH10 : (u_pre <= UINT_MAX)) (PreH11 : (0 <= v_pre)) (PreH12 : (v_pre <= UINT_MAX)) (PreH13 : ((u_pre + v_pre ) > 0)) ,
  TT && emp 
|--
  “ (0 <= retval) ” 
  &&  “ (retval < 32) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 < (Z.shiftr v_pre retval)) ” 
  &&  “ ((Z.shiftr v_pre retval) <= UINT_MAX) ” 
  &&  “ (0 < (Z.shiftr u_pre retval)) ” 
  &&  “ ((Z.shiftr u_pre retval) <= UINT_MAX) ” 
  &&  “ ((Z.land (Z.shiftr v_pre retval) 1) <> 0) ” 
  &&  “ ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (retval)) * (Zgcd ((Z.shiftr v_pre retval)) ((Z.shiftr u_pre retval))) )) ”
  &&  emp
) \/
(
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : ((Z.land (Z.shiftr u_pre retval) 1) = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH7 : (v_pre <> 0)) (PreH8 : (u_pre <> 0)) (PreH9 : (0 <= u_pre)) (PreH10 : (u_pre <= UINT_MAX)) (PreH11 : (0 <= v_pre)) (PreH12 : (v_pre <= UINT_MAX)) (PreH13 : ((u_pre + v_pre ) > 0)) ,
  TT && emp 
|--
  “ ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (retval)) * (Zgcd ((Z.shiftr v_pre retval)) ((Z.shiftr u_pre retval))) )) ” 
  &&  “ ((Z.land (Z.shiftr v_pre retval) 1) <> 0) ” 
  &&  “ ((Z.shiftr u_pre retval) <= UINT_MAX) ” 
  &&  “ (0 < (Z.shiftr u_pre retval)) ” 
  &&  “ ((Z.shiftr v_pre retval) <= UINT_MAX) ” 
  &&  “ (0 < (Z.shiftr v_pre retval)) ”
  &&  emp
).

Definition mpn_gcd_11_entail_wit_1_1_split_goal_1 := 
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : ((Z.land (Z.shiftr u_pre retval) 1) = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH7 : (v_pre <> 0)) (PreH8 : (u_pre <> 0)) (PreH9 : (0 <= u_pre)) (PreH10 : (u_pre <= UINT_MAX)) (PreH11 : (0 <= v_pre)) (PreH12 : (v_pre <= UINT_MAX)) (PreH13 : ((u_pre + v_pre ) > 0)) ,
  ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (retval)) * (Zgcd ((Z.shiftr v_pre retval)) ((Z.shiftr u_pre retval))) ))
.

Definition mpn_gcd_11_entail_wit_1_1_split_goal_2 := 
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : ((Z.land (Z.shiftr u_pre retval) 1) = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH7 : (v_pre <> 0)) (PreH8 : (u_pre <> 0)) (PreH9 : (0 <= u_pre)) (PreH10 : (u_pre <= UINT_MAX)) (PreH11 : (0 <= v_pre)) (PreH12 : (v_pre <= UINT_MAX)) (PreH13 : ((u_pre + v_pre ) > 0)) ,
  ((Z.land (Z.shiftr v_pre retval) 1) <> 0)
.

Definition mpn_gcd_11_entail_wit_1_1_split_goal_3 := 
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : ((Z.land (Z.shiftr u_pre retval) 1) = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH7 : (v_pre <> 0)) (PreH8 : (u_pre <> 0)) (PreH9 : (0 <= u_pre)) (PreH10 : (u_pre <= UINT_MAX)) (PreH11 : (0 <= v_pre)) (PreH12 : (v_pre <= UINT_MAX)) (PreH13 : ((u_pre + v_pre ) > 0)) ,
  ((Z.shiftr u_pre retval) <= UINT_MAX)
.

Definition mpn_gcd_11_entail_wit_1_1_split_goal_4 := 
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : ((Z.land (Z.shiftr u_pre retval) 1) = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH7 : (v_pre <> 0)) (PreH8 : (u_pre <> 0)) (PreH9 : (0 <= u_pre)) (PreH10 : (u_pre <= UINT_MAX)) (PreH11 : (0 <= v_pre)) (PreH12 : (v_pre <= UINT_MAX)) (PreH13 : ((u_pre + v_pre ) > 0)) ,
  (0 < (Z.shiftr u_pre retval))
.

Definition mpn_gcd_11_entail_wit_1_1_split_goal_5 := 
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : ((Z.land (Z.shiftr u_pre retval) 1) = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH7 : (v_pre <> 0)) (PreH8 : (u_pre <> 0)) (PreH9 : (0 <= u_pre)) (PreH10 : (u_pre <= UINT_MAX)) (PreH11 : (0 <= v_pre)) (PreH12 : (v_pre <= UINT_MAX)) (PreH13 : ((u_pre + v_pre ) > 0)) ,
  ((Z.shiftr v_pre retval) <= UINT_MAX)
.

Definition mpn_gcd_11_entail_wit_1_1_split_goal_6 := 
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : ((Z.land (Z.shiftr u_pre retval) 1) = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH7 : (v_pre <> 0)) (PreH8 : (u_pre <> 0)) (PreH9 : (0 <= u_pre)) (PreH10 : (u_pre <= UINT_MAX)) (PreH11 : (0 <= v_pre)) (PreH12 : (v_pre <= UINT_MAX)) (PreH13 : ((u_pre + v_pre ) > 0)) ,
  (0 < (Z.shiftr v_pre retval))
.

Definition mpn_gcd_11_entail_wit_1_2 := 
(
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : ((Z.land (Z.shiftr u_pre retval) 1) <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH7 : (v_pre <> 0)) (PreH8 : (u_pre <> 0)) (PreH9 : (0 <= u_pre)) (PreH10 : (u_pre <= UINT_MAX)) (PreH11 : (0 <= v_pre)) (PreH12 : (v_pre <= UINT_MAX)) (PreH13 : ((u_pre + v_pre ) > 0)) ,
  TT && emp 
|--
  “ (0 <= retval) ” 
  &&  “ (retval < 32) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 < (Z.shiftr u_pre retval)) ” 
  &&  “ ((Z.shiftr u_pre retval) <= UINT_MAX) ” 
  &&  “ (0 < (Z.shiftr v_pre retval)) ” 
  &&  “ ((Z.shiftr v_pre retval) <= UINT_MAX) ” 
  &&  “ ((Z.land (Z.shiftr u_pre retval) 1) <> 0) ” 
  &&  “ ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (retval)) * (Zgcd ((Z.shiftr u_pre retval)) ((Z.shiftr v_pre retval))) )) ”
  &&  emp
) \/
(
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : ((Z.land (Z.shiftr u_pre retval) 1) <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH7 : (v_pre <> 0)) (PreH8 : (u_pre <> 0)) (PreH9 : (0 <= u_pre)) (PreH10 : (u_pre <= UINT_MAX)) (PreH11 : (0 <= v_pre)) (PreH12 : (v_pre <= UINT_MAX)) (PreH13 : ((u_pre + v_pre ) > 0)) ,
  TT && emp 
|--
  “ ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (retval)) * (Zgcd ((Z.shiftr u_pre retval)) ((Z.shiftr v_pre retval))) )) ” 
  &&  “ ((Z.shiftr v_pre retval) <= UINT_MAX) ” 
  &&  “ (0 < (Z.shiftr v_pre retval)) ” 
  &&  “ ((Z.shiftr u_pre retval) <= UINT_MAX) ” 
  &&  “ (0 < (Z.shiftr u_pre retval)) ”
  &&  emp
).

Definition mpn_gcd_11_entail_wit_1_2_split_goal_1 := 
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : ((Z.land (Z.shiftr u_pre retval) 1) <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH7 : (v_pre <> 0)) (PreH8 : (u_pre <> 0)) (PreH9 : (0 <= u_pre)) (PreH10 : (u_pre <= UINT_MAX)) (PreH11 : (0 <= v_pre)) (PreH12 : (v_pre <= UINT_MAX)) (PreH13 : ((u_pre + v_pre ) > 0)) ,
  ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (retval)) * (Zgcd ((Z.shiftr u_pre retval)) ((Z.shiftr v_pre retval))) ))
.

Definition mpn_gcd_11_entail_wit_1_2_split_goal_2 := 
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : ((Z.land (Z.shiftr u_pre retval) 1) <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH7 : (v_pre <> 0)) (PreH8 : (u_pre <> 0)) (PreH9 : (0 <= u_pre)) (PreH10 : (u_pre <= UINT_MAX)) (PreH11 : (0 <= v_pre)) (PreH12 : (v_pre <= UINT_MAX)) (PreH13 : ((u_pre + v_pre ) > 0)) ,
  ((Z.shiftr v_pre retval) <= UINT_MAX)
.

Definition mpn_gcd_11_entail_wit_1_2_split_goal_3 := 
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : ((Z.land (Z.shiftr u_pre retval) 1) <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH7 : (v_pre <> 0)) (PreH8 : (u_pre <> 0)) (PreH9 : (0 <= u_pre)) (PreH10 : (u_pre <= UINT_MAX)) (PreH11 : (0 <= v_pre)) (PreH12 : (v_pre <= UINT_MAX)) (PreH13 : ((u_pre + v_pre ) > 0)) ,
  (0 < (Z.shiftr v_pre retval))
.

Definition mpn_gcd_11_entail_wit_1_2_split_goal_4 := 
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : ((Z.land (Z.shiftr u_pre retval) 1) <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH7 : (v_pre <> 0)) (PreH8 : (u_pre <> 0)) (PreH9 : (0 <= u_pre)) (PreH10 : (u_pre <= UINT_MAX)) (PreH11 : (0 <= v_pre)) (PreH12 : (v_pre <= UINT_MAX)) (PreH13 : ((u_pre + v_pre ) > 0)) ,
  ((Z.shiftr u_pre retval) <= UINT_MAX)
.

Definition mpn_gcd_11_entail_wit_1_2_split_goal_5 := 
forall (v_pre: Z) (u_pre: Z) (odd: Z) (retval: Z) (PreH1 : ((Z.land (Z.shiftr u_pre retval) 1) <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval < 32)) (PreH4 : (odd > 0)) (PreH5 : ((odd % ( 2 ) ) = 1)) (PreH6 : ((Z.lor u_pre v_pre) = (odd * (Z.pow (2) (retval)) ))) (PreH7 : (v_pre <> 0)) (PreH8 : (u_pre <> 0)) (PreH9 : (0 <= u_pre)) (PreH10 : (u_pre <= UINT_MAX)) (PreH11 : (0 <= v_pre)) (PreH12 : (v_pre <= UINT_MAX)) (PreH13 : ((u_pre + v_pre ) > 0)) ,
  (0 < (Z.shiftr u_pre retval))
.

Definition mpn_gcd_11_entail_wit_2 := 
(
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land v 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  TT && emp 
|--
  “ (0 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 < u) ” 
  &&  “ (u <= UINT_MAX) ” 
  &&  “ (0 < (Z.shiftr v 1)) ” 
  &&  “ ((Z.shiftr v 1) <= UINT_MAX) ” 
  &&  “ ((Z.land u 1) <> 0) ” 
  &&  “ ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) ((Z.shiftr v 1))) )) ”
  &&  emp
) \/
(
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land v 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  TT && emp 
|--
  “ ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) ((Z.shiftr v 1))) )) ” 
  &&  “ ((Z.shiftr v 1) <= UINT_MAX) ” 
  &&  “ (0 < (Z.shiftr v 1)) ”
  &&  emp
).

Definition mpn_gcd_11_entail_wit_2_split_goal_1 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land v 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) ((Z.shiftr v 1))) ))
.

Definition mpn_gcd_11_entail_wit_2_split_goal_2 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land v 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((Z.shiftr v 1) <= UINT_MAX)
.

Definition mpn_gcd_11_entail_wit_2_split_goal_3 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land v 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  (0 < (Z.shiftr v 1))
.

Definition mpn_gcd_11_entail_wit_3 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land v 1) <> 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  TT && emp 
|--
  “ (0 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 < u) ” 
  &&  “ (u <= UINT_MAX) ” 
  &&  “ (0 < v) ” 
  &&  “ (v <= UINT_MAX) ” 
  &&  “ ((Z.land u 1) <> 0) ” 
  &&  “ ((Z.land v 1) <> 0) ” 
  &&  “ ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) )) ”
  &&  emp
.

Definition mpn_gcd_11_entail_wit_4 := 
(
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land u 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land v 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  TT && emp 
|--
  “ (0 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 < (Z.shiftr u 1)) ” 
  &&  “ ((Z.shiftr u 1) <= UINT_MAX) ” 
  &&  “ (0 < v) ” 
  &&  “ (v <= UINT_MAX) ” 
  &&  “ ((Z.land v 1) <> 0) ” 
  &&  “ ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd ((Z.shiftr u 1)) (v)) )) ”
  &&  emp
) \/
(
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land u 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land v 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  TT && emp 
|--
  “ ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd ((Z.shiftr u 1)) (v)) )) ” 
  &&  “ ((Z.shiftr u 1) <= UINT_MAX) ” 
  &&  “ (0 < (Z.shiftr u 1)) ”
  &&  emp
).

Definition mpn_gcd_11_entail_wit_4_split_goal_1 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land u 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land v 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd ((Z.shiftr u 1)) (v)) ))
.

Definition mpn_gcd_11_entail_wit_4_split_goal_2 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land u 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land v 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((Z.shiftr u 1) <= UINT_MAX)
.

Definition mpn_gcd_11_entail_wit_4_split_goal_3 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land u 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land v 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  (0 < (Z.shiftr u 1))
.

Definition mpn_gcd_11_entail_wit_5 := 
(
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (u > v)) (PreH2 : (u <> v)) (PreH3 : (0 <= shift)) (PreH4 : (shift < 32)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= UINT_MAX)) (PreH9 : (0 < u)) (PreH10 : (u <= UINT_MAX)) (PreH11 : (0 < v)) (PreH12 : (v <= UINT_MAX)) (PreH13 : ((Z.land u 1) <> 0)) (PreH14 : ((Z.land v 1) <> 0)) (PreH15 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  TT && emp 
|--
  “ (0 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 < (Z.shiftr (u - v ) 1)) ” 
  &&  “ ((Z.shiftr (u - v ) 1) <= UINT_MAX) ” 
  &&  “ (0 < v) ” 
  &&  “ (v <= UINT_MAX) ” 
  &&  “ ((Z.land v 1) <> 0) ” 
  &&  “ ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd ((Z.shiftr (u - v ) 1)) (v)) )) ”
  &&  emp
) \/
(
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (u > v)) (PreH2 : (u <> v)) (PreH3 : (0 <= shift)) (PreH4 : (shift < 32)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= UINT_MAX)) (PreH9 : (0 < u)) (PreH10 : (u <= UINT_MAX)) (PreH11 : (0 < v)) (PreH12 : (v <= UINT_MAX)) (PreH13 : ((Z.land u 1) <> 0)) (PreH14 : ((Z.land v 1) <> 0)) (PreH15 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  TT && emp 
|--
  “ ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd ((Z.shiftr (u - v ) 1)) (v)) )) ” 
  &&  “ ((Z.shiftr (u - v ) 1) <= UINT_MAX) ” 
  &&  “ (0 < (Z.shiftr (u - v ) 1)) ”
  &&  emp
).

Definition mpn_gcd_11_entail_wit_5_split_goal_1 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (u > v)) (PreH2 : (u <> v)) (PreH3 : (0 <= shift)) (PreH4 : (shift < 32)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= UINT_MAX)) (PreH9 : (0 < u)) (PreH10 : (u <= UINT_MAX)) (PreH11 : (0 < v)) (PreH12 : (v <= UINT_MAX)) (PreH13 : ((Z.land u 1) <> 0)) (PreH14 : ((Z.land v 1) <> 0)) (PreH15 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd ((Z.shiftr (u - v ) 1)) (v)) ))
.

Definition mpn_gcd_11_entail_wit_5_split_goal_2 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (u > v)) (PreH2 : (u <> v)) (PreH3 : (0 <= shift)) (PreH4 : (shift < 32)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= UINT_MAX)) (PreH9 : (0 < u)) (PreH10 : (u <= UINT_MAX)) (PreH11 : (0 < v)) (PreH12 : (v <= UINT_MAX)) (PreH13 : ((Z.land u 1) <> 0)) (PreH14 : ((Z.land v 1) <> 0)) (PreH15 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((Z.shiftr (u - v ) 1) <= UINT_MAX)
.

Definition mpn_gcd_11_entail_wit_5_split_goal_3 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (u > v)) (PreH2 : (u <> v)) (PreH3 : (0 <= shift)) (PreH4 : (shift < 32)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= UINT_MAX)) (PreH9 : (0 < u)) (PreH10 : (u <= UINT_MAX)) (PreH11 : (0 < v)) (PreH12 : (v <= UINT_MAX)) (PreH13 : ((Z.land u 1) <> 0)) (PreH14 : ((Z.land v 1) <> 0)) (PreH15 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  (0 < (Z.shiftr (u - v ) 1))
.

Definition mpn_gcd_11_entail_wit_6 := 
(
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land v 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  TT && emp 
|--
  “ (0 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 < u) ” 
  &&  “ (u <= UINT_MAX) ” 
  &&  “ (0 < (Z.shiftr v 1)) ” 
  &&  “ ((Z.shiftr v 1) <= UINT_MAX) ” 
  &&  “ ((Z.land u 1) <> 0) ” 
  &&  “ ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) ((Z.shiftr v 1))) )) ”
  &&  emp
) \/
(
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land v 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  TT && emp 
|--
  “ ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) ((Z.shiftr v 1))) )) ” 
  &&  “ ((Z.shiftr v 1) <= UINT_MAX) ” 
  &&  “ (0 < (Z.shiftr v 1)) ”
  &&  emp
).

Definition mpn_gcd_11_entail_wit_6_split_goal_1 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land v 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) ((Z.shiftr v 1))) ))
.

Definition mpn_gcd_11_entail_wit_6_split_goal_2 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land v 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((Z.shiftr v 1) <= UINT_MAX)
.

Definition mpn_gcd_11_entail_wit_6_split_goal_3 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land v 1) = 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  (0 < (Z.shiftr v 1))
.

Definition mpn_gcd_11_entail_wit_7 := 
(
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (u <= v)) (PreH2 : (u <> v)) (PreH3 : (0 <= shift)) (PreH4 : (shift < 32)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= UINT_MAX)) (PreH9 : (0 < u)) (PreH10 : (u <= UINT_MAX)) (PreH11 : (0 < v)) (PreH12 : (v <= UINT_MAX)) (PreH13 : ((Z.land u 1) <> 0)) (PreH14 : ((Z.land v 1) <> 0)) (PreH15 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  TT && emp 
|--
  “ (0 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 < u) ” 
  &&  “ (u <= UINT_MAX) ” 
  &&  “ (0 < (Z.shiftr (v - u ) 1)) ” 
  &&  “ ((Z.shiftr (v - u ) 1) <= UINT_MAX) ” 
  &&  “ ((Z.land u 1) <> 0) ” 
  &&  “ ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) ((Z.shiftr (v - u ) 1))) )) ”
  &&  emp
) \/
(
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (u <= v)) (PreH2 : (u <> v)) (PreH3 : (0 <= shift)) (PreH4 : (shift < 32)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= UINT_MAX)) (PreH9 : (0 < u)) (PreH10 : (u <= UINT_MAX)) (PreH11 : (0 < v)) (PreH12 : (v <= UINT_MAX)) (PreH13 : ((Z.land u 1) <> 0)) (PreH14 : ((Z.land v 1) <> 0)) (PreH15 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  TT && emp 
|--
  “ ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) ((Z.shiftr (v - u ) 1))) )) ” 
  &&  “ ((Z.shiftr (v - u ) 1) <= UINT_MAX) ” 
  &&  “ (0 < (Z.shiftr (v - u ) 1)) ”
  &&  emp
).

Definition mpn_gcd_11_entail_wit_7_split_goal_1 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (u <= v)) (PreH2 : (u <> v)) (PreH3 : (0 <= shift)) (PreH4 : (shift < 32)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= UINT_MAX)) (PreH9 : (0 < u)) (PreH10 : (u <= UINT_MAX)) (PreH11 : (0 < v)) (PreH12 : (v <= UINT_MAX)) (PreH13 : ((Z.land u 1) <> 0)) (PreH14 : ((Z.land v 1) <> 0)) (PreH15 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) ((Z.shiftr (v - u ) 1))) ))
.

Definition mpn_gcd_11_entail_wit_7_split_goal_2 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (u <= v)) (PreH2 : (u <> v)) (PreH3 : (0 <= shift)) (PreH4 : (shift < 32)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= UINT_MAX)) (PreH9 : (0 < u)) (PreH10 : (u <= UINT_MAX)) (PreH11 : (0 < v)) (PreH12 : (v <= UINT_MAX)) (PreH13 : ((Z.land u 1) <> 0)) (PreH14 : ((Z.land v 1) <> 0)) (PreH15 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((Z.shiftr (v - u ) 1) <= UINT_MAX)
.

Definition mpn_gcd_11_entail_wit_7_split_goal_3 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (u <= v)) (PreH2 : (u <> v)) (PreH3 : (0 <= shift)) (PreH4 : (shift < 32)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= UINT_MAX)) (PreH9 : (0 < u)) (PreH10 : (u <= UINT_MAX)) (PreH11 : (0 < v)) (PreH12 : (v <= UINT_MAX)) (PreH13 : ((Z.land u 1) <> 0)) (PreH14 : ((Z.land v 1) <> 0)) (PreH15 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  (0 < (Z.shiftr (v - u ) 1))
.

Definition mpn_gcd_11_entail_wit_8_1 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land u 1) <> 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land v 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  TT && emp 
|--
  “ (0 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 < u) ” 
  &&  “ (u <= UINT_MAX) ” 
  &&  “ (0 < v) ” 
  &&  “ (v <= UINT_MAX) ” 
  &&  “ ((Z.land u 1) <> 0) ” 
  &&  “ ((Z.land v 1) <> 0) ” 
  &&  “ ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) )) ”
  &&  emp
.

Definition mpn_gcd_11_entail_wit_8_2 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : ((Z.land v 1) <> 0)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  TT && emp 
|--
  “ (0 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ (0 < u) ” 
  &&  “ (u <= UINT_MAX) ” 
  &&  “ (0 < v) ” 
  &&  “ (v <= UINT_MAX) ” 
  &&  “ ((Z.land u 1) <> 0) ” 
  &&  “ ((Z.land v 1) <> 0) ” 
  &&  “ ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) )) ”
  &&  emp
.

Definition mpn_gcd_11_return_wit_1 := 
(
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (u = v)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Z.land v 1) <> 0)) (PreH14 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits ((Z.shiftl u shift)) (32)) = (Zgcd (u_pre) (v_pre))) ”
  &&  emp
) \/
(
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (u = v)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Z.land v 1) <> 0)) (PreH14 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits ((Z.shiftl u shift)) (32)) = (Zgcd (u_pre) (v_pre))) ”
  &&  emp
).

Definition mpn_gcd_11_return_wit_1_split_goal_1 := 
forall (v_pre: Z) (u_pre: Z) (v: Z) (u: Z) (shift: Z) (PreH1 : (u = v)) (PreH2 : (0 <= shift)) (PreH3 : (shift < 32)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (0 <= v_pre)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (0 < u)) (PreH9 : (u <= UINT_MAX)) (PreH10 : (0 < v)) (PreH11 : (v <= UINT_MAX)) (PreH12 : ((Z.land u 1) <> 0)) (PreH13 : ((Z.land v 1) <> 0)) (PreH14 : ((Zgcd (u_pre) (v_pre)) = ((Z.pow (2) (shift)) * (Zgcd (u) (v)) ))) ,
  ((unsigned_last_nbits ((Z.shiftl u shift)) (32)) = (Zgcd (u_pre) (v_pre)))
.

Definition mpn_gcd_11_return_wit_2 := 
(
forall (v_pre: Z) (u_pre: Z) (PreH1 : (v_pre = 0)) (PreH2 : (u_pre <> 0)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (0 <= v_pre)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : ((u_pre + v_pre ) > 0)) ,
  TT && emp 
|--
  “ (u_pre = (Zgcd (u_pre) (v_pre))) ”
  &&  emp
) \/
(
forall (v_pre: Z) (u_pre: Z) (PreH1 : (v_pre = 0)) (PreH2 : (u_pre <> 0)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (0 <= v_pre)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : ((u_pre + v_pre ) > 0)) ,
  TT && emp 
|--
  “ (u_pre = (Zgcd (u_pre) (v_pre))) ”
  &&  emp
).

Definition mpn_gcd_11_return_wit_2_split_goal_1 := 
forall (v_pre: Z) (u_pre: Z) (PreH1 : (v_pre = 0)) (PreH2 : (u_pre <> 0)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (0 <= v_pre)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : ((u_pre + v_pre ) > 0)) ,
  (u_pre = (Zgcd (u_pre) (v_pre)))
.

Definition mpn_gcd_11_return_wit_3 := 
(
forall (v_pre: Z) (u_pre: Z) (PreH1 : (u_pre = 0)) (PreH2 : (0 <= u_pre)) (PreH3 : (u_pre <= UINT_MAX)) (PreH4 : (0 <= v_pre)) (PreH5 : (v_pre <= UINT_MAX)) (PreH6 : ((u_pre + v_pre ) > 0)) ,
  TT && emp 
|--
  “ (v_pre = (Zgcd (u_pre) (v_pre))) ”
  &&  emp
) \/
(
forall (v_pre: Z) (u_pre: Z) (PreH1 : (u_pre = 0)) (PreH2 : (0 <= u_pre)) (PreH3 : (u_pre <= UINT_MAX)) (PreH4 : (0 <= v_pre)) (PreH5 : (v_pre <= UINT_MAX)) (PreH6 : ((u_pre + v_pre ) > 0)) ,
  TT && emp 
|--
  “ (v_pre = (Zgcd (u_pre) (v_pre))) ”
  &&  emp
).

Definition mpn_gcd_11_return_wit_3_split_goal_1 := 
forall (v_pre: Z) (u_pre: Z) (PreH1 : (u_pre = 0)) (PreH2 : (0 <= u_pre)) (PreH3 : (u_pre <= UINT_MAX)) (PreH4 : (0 <= v_pre)) (PreH5 : (v_pre <= UINT_MAX)) (PreH6 : ((u_pre + v_pre ) > 0)) ,
  (v_pre = (Zgcd (u_pre) (v_pre)))
.

Definition mpn_gcd_11_partial_solve_wit_1_pure := 
(
forall (v_pre: Z) (u_pre: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (u_pre <> 0)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (0 <= v_pre)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : ((u_pre + v_pre ) > 0)) ,
  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "v" ) )) # UInt  |-> v_pre)
|--
  “ ((Z.lor u_pre v_pre) <= UINT_MAX) ” 
  &&  “ (0 < (Z.lor u_pre v_pre)) ”
) \/
(
forall (v_pre: Z) (u_pre: Z) (PreH1 : (v_pre >= 0)) (PreH2 : (u_pre >= 0)) (PreH3 : (v_pre <> 0)) (PreH4 : (u_pre <> 0)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= UINT_MAX)) (PreH9 : ((u_pre + v_pre ) > 0)) ,
  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "v" ) )) # UInt  |-> v_pre)
|--
  “ (0 < (Z.lor u_pre v_pre)) ” 
  &&  “ ((Z.lor u_pre v_pre) <= UINT_MAX) ”
).

Definition mpn_gcd_11_partial_solve_wit_1_pure_split_goal_1 := 
forall (v_pre: Z) (u_pre: Z) (PreH1 : (v_pre >= 0)) (PreH2 : (u_pre >= 0)) (PreH3 : (v_pre <> 0)) (PreH4 : (u_pre <> 0)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= UINT_MAX)) (PreH9 : ((u_pre + v_pre ) > 0)) ,
  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "v" ) )) # UInt  |-> v_pre)
|--
  “ (0 < (Z.lor u_pre v_pre)) ”
.

Definition mpn_gcd_11_partial_solve_wit_1_pure_split_goal_2 := 
forall (v_pre: Z) (u_pre: Z) (PreH1 : (v_pre >= 0)) (PreH2 : (u_pre >= 0)) (PreH3 : (v_pre <> 0)) (PreH4 : (u_pre <> 0)) (PreH5 : (0 <= u_pre)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= UINT_MAX)) (PreH9 : ((u_pre + v_pre ) > 0)) ,
  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "v" ) )) # UInt  |-> v_pre)
|--
  “ ((Z.lor u_pre v_pre) <= UINT_MAX) ”
.

Definition mpn_gcd_11_partial_solve_wit_1_aux := 
forall (v_pre: Z) (u_pre: Z) (PreH1 : (v_pre <> 0)) (PreH2 : (u_pre <> 0)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (0 <= v_pre)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : ((u_pre + v_pre ) > 0)) ,
  TT && emp 
|--
  “ ((Z.lor u_pre v_pre) <= UINT_MAX) ” 
  &&  “ (0 < (Z.lor u_pre v_pre)) ” 
  &&  “ (v_pre <> 0) ” 
  &&  “ (u_pre <> 0) ” 
  &&  “ (0 <= u_pre) ” 
  &&  “ (u_pre <= UINT_MAX) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= UINT_MAX) ” 
  &&  “ ((u_pre + v_pre ) > 0) ”
  &&  emp
.

Definition mpn_gcd_11_partial_solve_wit_1 := mpn_gcd_11_partial_solve_wit_1_pure -> mpn_gcd_11_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_gmp_ctz_safety_wit_1 : gmp_ctz_safety_wit_1.
Axiom proof_of_gmp_ctz_return_wit_1 : gmp_ctz_return_wit_1.
Axiom proof_of_gmp_ctz_partial_solve_wit_1_pure : gmp_ctz_partial_solve_wit_1_pure.
Axiom proof_of_gmp_ctz_partial_solve_wit_1 : gmp_ctz_partial_solve_wit_1.
Axiom proof_of_mpn_gcd_11_safety_wit_1 : mpn_gcd_11_safety_wit_1.
Axiom proof_of_mpn_gcd_11_safety_wit_2 : mpn_gcd_11_safety_wit_2.
Axiom proof_of_mpn_gcd_11_safety_wit_3 : mpn_gcd_11_safety_wit_3.
Axiom proof_of_mpn_gcd_11_safety_wit_4 : mpn_gcd_11_safety_wit_4.
Axiom proof_of_mpn_gcd_11_safety_wit_5 : mpn_gcd_11_safety_wit_5.
Axiom proof_of_mpn_gcd_11_safety_wit_6 : mpn_gcd_11_safety_wit_6.
Axiom proof_of_mpn_gcd_11_safety_wit_7 : mpn_gcd_11_safety_wit_7.
Axiom proof_of_mpn_gcd_11_safety_wit_8 : mpn_gcd_11_safety_wit_8.
Axiom proof_of_mpn_gcd_11_safety_wit_9 : mpn_gcd_11_safety_wit_9.
Axiom proof_of_mpn_gcd_11_safety_wit_10 : mpn_gcd_11_safety_wit_10.
Axiom proof_of_mpn_gcd_11_safety_wit_11 : mpn_gcd_11_safety_wit_11.
Axiom proof_of_mpn_gcd_11_safety_wit_12 : mpn_gcd_11_safety_wit_12.
Axiom proof_of_mpn_gcd_11_safety_wit_13 : mpn_gcd_11_safety_wit_13.
Axiom proof_of_mpn_gcd_11_safety_wit_14 : mpn_gcd_11_safety_wit_14.
Axiom proof_of_mpn_gcd_11_safety_wit_15 : mpn_gcd_11_safety_wit_15.
Axiom proof_of_mpn_gcd_11_safety_wit_16 : mpn_gcd_11_safety_wit_16.
Axiom proof_of_mpn_gcd_11_safety_wit_17 : mpn_gcd_11_safety_wit_17.
Axiom proof_of_mpn_gcd_11_safety_wit_18 : mpn_gcd_11_safety_wit_18.
Axiom proof_of_mpn_gcd_11_safety_wit_19 : mpn_gcd_11_safety_wit_19.
Axiom proof_of_mpn_gcd_11_safety_wit_20 : mpn_gcd_11_safety_wit_20.
Axiom proof_of_mpn_gcd_11_safety_wit_21 : mpn_gcd_11_safety_wit_21.
Axiom proof_of_mpn_gcd_11_safety_wit_22 : mpn_gcd_11_safety_wit_22.
Axiom proof_of_mpn_gcd_11_safety_wit_23 : mpn_gcd_11_safety_wit_23.
Axiom proof_of_mpn_gcd_11_entail_wit_1_1 : mpn_gcd_11_entail_wit_1_1.
Axiom proof_of_mpn_gcd_11_entail_wit_1_2 : mpn_gcd_11_entail_wit_1_2.
Axiom proof_of_mpn_gcd_11_entail_wit_2 : mpn_gcd_11_entail_wit_2.
Axiom proof_of_mpn_gcd_11_entail_wit_3 : mpn_gcd_11_entail_wit_3.
Axiom proof_of_mpn_gcd_11_entail_wit_4 : mpn_gcd_11_entail_wit_4.
Axiom proof_of_mpn_gcd_11_entail_wit_5 : mpn_gcd_11_entail_wit_5.
Axiom proof_of_mpn_gcd_11_entail_wit_6 : mpn_gcd_11_entail_wit_6.
Axiom proof_of_mpn_gcd_11_entail_wit_7 : mpn_gcd_11_entail_wit_7.
Axiom proof_of_mpn_gcd_11_entail_wit_8_1 : mpn_gcd_11_entail_wit_8_1.
Axiom proof_of_mpn_gcd_11_entail_wit_8_2 : mpn_gcd_11_entail_wit_8_2.
Axiom proof_of_mpn_gcd_11_return_wit_1 : mpn_gcd_11_return_wit_1.
Axiom proof_of_mpn_gcd_11_return_wit_2 : mpn_gcd_11_return_wit_2.
Axiom proof_of_mpn_gcd_11_return_wit_3 : mpn_gcd_11_return_wit_3.
Axiom proof_of_mpn_gcd_11_partial_solve_wit_1_pure : mpn_gcd_11_partial_solve_wit_1_pure.
Axiom proof_of_mpn_gcd_11_partial_solve_wit_1 : mpn_gcd_11_partial_solve_wit_1.

End VC_Correct.
