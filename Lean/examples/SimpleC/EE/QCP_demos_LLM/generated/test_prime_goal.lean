import SimpleC.SL.SeparationLogic

import SimpleC.EE.QCP_demos_LLM.simple_arith.test_prime_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.test_prime_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance test_prime_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def test_prime_safety_wit_1 : Prop :=
  forall (x_pre : Int) (PreH1 : ((0 : Int) <= x_pre)) (PreH2 : (x_pre <= 1000000000)) ,
  ((( &( "x" ) )) # UInt |-> (x_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def test_prime_safety_wit_2 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre < 2)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  ((( &( "x" ) )) # UInt |-> (x_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def test_prime_safety_wit_3 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre >= 2)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  ((( &( "d" ) )) # Int |->_)
  ** ((( &( "x" ) )) # UInt |-> (x_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def test_prime_safety_wit_4 : Prop :=
  forall (x_pre : Int) (d : Int) (PreH1 : (d < x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= x_pre)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ¬((HasFactorBetween x_pre 2 d))) ,
  ((( &( "x" ) )) # UInt |-> (x_pre))
  ** ((( &( "d" ) )) # Int |-> (d))
|--
  “ (d ≠ (0 : Int)) ”

noncomputable def test_prime_safety_wit_5 : Prop :=
  forall (x_pre : Int) (d : Int) (PreH1 : (d < x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= x_pre)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ¬((HasFactorBetween x_pre 2 d))) ,
  ((( &( "x" ) )) # UInt |-> (x_pre))
  ** ((( &( "d" ) )) # Int |-> (d))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def test_prime_safety_wit_6 : Prop :=
  forall (x_pre : Int) (d : Int) (PreH1 : ((Z.rem x_pre d) = (0 : Int))) (PreH2 : (d < x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= x_pre)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ¬((HasFactorBetween x_pre 2 d))) ,
  ((( &( "x" ) )) # UInt |-> (x_pre))
  ** ((( &( "d" ) )) # Int |-> (d))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def test_prime_safety_wit_7 : Prop :=
  forall (x_pre : Int) (d : Int) (PreH1 : ((Z.rem x_pre d) ≠ (0 : Int))) (PreH2 : (d < x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= x_pre)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ¬((HasFactorBetween x_pre 2 d))) ,
  ((( &( "x" ) )) # UInt |-> (x_pre))
  ** ((( &( "d" ) )) # Int |-> (d))
|--
  “ ((d + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (d + 1)) ”

noncomputable def test_prime_safety_wit_8 : Prop :=
  forall (x_pre : Int) (d : Int) (PreH1 : (d >= x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= x_pre)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ¬((HasFactorBetween x_pre 2 d))) ,
  ((( &( "x" ) )) # UInt |-> (x_pre))
  ** ((( &( "d" ) )) # Int |-> (d))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def test_prime_entail_wit_1 : Prop :=
  (
forall (x_pre : Int) (PreH1 : (x_pre >= 2)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (2 <= 2) ” &&
  “ (2 <= x_pre) ” &&
  “ (2 <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ ¬((HasFactorBetween x_pre 2 2)) ”
  &&  emp
) \/
(
forall (x_pre : Int) (PreH1 : (x_pre >= 2)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  TT && emp 
|--
  “ ¬((HasFactorBetween x_pre 2 2)) ”
  &&  emp
)

noncomputable def test_prime_entail_wit_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre >= 2)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  ¬((HasFactorBetween x_pre 2 2))

noncomputable def test_prime_entail_wit_2 : Prop :=
  (
forall (x_pre : Int) (d : Int) (PreH1 : ((Z.rem x_pre d) ≠ (0 : Int))) (PreH2 : (d < x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= x_pre)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ¬((HasFactorBetween x_pre 2 d))) ,
  TT && emp 
|--
  “ (2 <= (d + 1)) ” &&
  “ ((d + 1) <= x_pre) ” &&
  “ (2 <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ ¬((HasFactorBetween x_pre 2 (d + 1))) ”
  &&  emp
) \/
(
forall (x_pre : Int) (d : Int) (PreH1 : ((Z.rem x_pre d) ≠ (0 : Int))) (PreH2 : (d < x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= x_pre)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ¬((HasFactorBetween x_pre 2 d))) ,
  TT && emp 
|--
  “ ¬((HasFactorBetween x_pre 2 (d + 1))) ”
  &&  emp
)

noncomputable def test_prime_entail_wit_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (d : Int) (PreH1 : ((Z.rem x_pre d) ≠ (0 : Int))) (PreH2 : (d < x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= x_pre)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ¬((HasFactorBetween x_pre 2 d))) ,
  ¬((HasFactorBetween x_pre 2 (d + 1)))

noncomputable def test_prime_return_wit_1 : Prop :=
  (
forall (x_pre : Int) (d : Int) (PreH1 : (d >= x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= x_pre)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ¬((HasFactorBetween x_pre 2 d))) ,
  TT && emp 
|--
  “ (1 = 1) ” &&
  “ (prime x_pre) ”
  &&  emp
) \/
(
forall (x_pre : Int) (d : Int) (PreH1 : (d >= x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= x_pre)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ¬((HasFactorBetween x_pre 2 d))) ,
  TT && emp 
|--
  “ (prime x_pre) ”
  &&  emp
)

noncomputable def test_prime_return_wit_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (d : Int) (PreH1 : (d >= x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= x_pre)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ¬((HasFactorBetween x_pre 2 d))) ,
  (prime x_pre)

noncomputable def test_prime_return_wit_2 : Prop :=
  (
forall (x_pre : Int) (d : Int) (PreH1 : ((Z.rem x_pre d) = (0 : Int))) (PreH2 : (d < x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= x_pre)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ¬((HasFactorBetween x_pre 2 d))) ,
  TT && emp 
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ¬((prime x_pre)) ”
  &&  emp
) \/
(
forall (x_pre : Int) (d : Int) (PreH1 : ((Z.rem x_pre d) = (0 : Int))) (PreH2 : (d < x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= x_pre)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ¬((HasFactorBetween x_pre 2 d))) ,
  TT && emp 
|--
  “ ¬((prime x_pre)) ”
  &&  emp
)

noncomputable def test_prime_return_wit_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (d : Int) (PreH1 : ((Z.rem x_pre d) = (0 : Int))) (PreH2 : (d < x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= x_pre)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ¬((HasFactorBetween x_pre 2 d))) ,
  ¬((prime x_pre))

noncomputable def test_prime_return_wit_3 : Prop :=
  (
forall (x_pre : Int) (PreH1 : (x_pre < 2)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  TT && emp 
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ¬((prime x_pre)) ”
  &&  emp
) \/
(
forall (x_pre : Int) (PreH1 : (x_pre < 2)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  TT && emp 
|--
  “ ¬((prime x_pre)) ”
  &&  emp
)

noncomputable def test_prime_return_wit_3_split_goal_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre < 2)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  ¬((prime x_pre))

noncomputable def test_prime_sqrt_safety_wit_1 : Prop :=
  forall (x_pre : Int) (PreH1 : ((0 : Int) <= x_pre)) (PreH2 : (x_pre <= 1000000000)) ,
  ((( &( "x" ) )) # UInt |-> (x_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def test_prime_sqrt_safety_wit_2 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre < 2)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  ((( &( "x" ) )) # UInt |-> (x_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def test_prime_sqrt_safety_wit_3 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre >= 2)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  ((( &( "d" ) )) # Int |->_)
  ** ((( &( "x" ) )) # UInt |-> (x_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def test_prime_sqrt_safety_wit_4 : Prop :=
  forall (x_pre : Int) (d : Int) (PreH1 : (2 <= d)) (PreH2 : (d <= 31624)) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 1000000000)) (PreH5 : ¬((HasFactorBetween x_pre 2 d))) ,
  ((( &( "x" ) )) # UInt |-> (x_pre))
  ** ((( &( "d" ) )) # Int |-> (d))
|--
  “ ((d * d) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (d * d)) ”

noncomputable def test_prime_sqrt_safety_wit_5 : Prop :=
  forall (x_pre : Int) (d : Int) (PreH1 : ((d * d) <= x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= 31624)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ¬((HasFactorBetween x_pre 2 d))) ,
  ((( &( "x" ) )) # UInt |-> (x_pre))
  ** ((( &( "d" ) )) # Int |-> (d))
|--
  “ (d ≠ (0 : Int)) ”

noncomputable def test_prime_sqrt_safety_wit_6 : Prop :=
  forall (x_pre : Int) (d : Int) (PreH1 : ((d * d) <= x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= 31624)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ¬((HasFactorBetween x_pre 2 d))) ,
  ((( &( "x" ) )) # UInt |-> (x_pre))
  ** ((( &( "d" ) )) # Int |-> (d))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def test_prime_sqrt_safety_wit_7 : Prop :=
  forall (x_pre : Int) (d : Int) (PreH1 : ((Z.rem x_pre d) = (0 : Int))) (PreH2 : ((d * d) <= x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= 31624)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ¬((HasFactorBetween x_pre 2 d))) ,
  ((( &( "x" ) )) # UInt |-> (x_pre))
  ** ((( &( "d" ) )) # Int |-> (d))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def test_prime_sqrt_safety_wit_8 : Prop :=
  forall (x_pre : Int) (d : Int) (PreH1 : ((Z.rem x_pre d) ≠ (0 : Int))) (PreH2 : ((d * d) <= x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= 31624)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ¬((HasFactorBetween x_pre 2 d))) ,
  ((( &( "x" ) )) # UInt |-> (x_pre))
  ** ((( &( "d" ) )) # Int |-> (d))
|--
  “ ((d + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (d + 1)) ”

noncomputable def test_prime_sqrt_safety_wit_9 : Prop :=
  forall (x_pre : Int) (d : Int) (PreH1 : ((d * d) > x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= 31624)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ¬((HasFactorBetween x_pre 2 d))) ,
  ((( &( "x" ) )) # UInt |-> (x_pre))
  ** ((( &( "d" ) )) # Int |-> (d))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def test_prime_sqrt_entail_wit_1 : Prop :=
  (
forall (x_pre : Int) (PreH1 : (x_pre >= 2)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (2 <= 2) ” &&
  “ (2 <= 31624) ” &&
  “ (2 <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ ¬((HasFactorBetween x_pre 2 2)) ”
  &&  emp
) \/
(
forall (x_pre : Int) (PreH1 : (x_pre >= 2)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  TT && emp 
|--
  “ ¬((HasFactorBetween x_pre 2 2)) ”
  &&  emp
)

noncomputable def test_prime_sqrt_entail_wit_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre >= 2)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  ¬((HasFactorBetween x_pre 2 2))

noncomputable def test_prime_sqrt_entail_wit_2 : Prop :=
  (
forall (x_pre : Int) (d : Int) (PreH1 : ((Z.rem x_pre d) ≠ (0 : Int))) (PreH2 : ((d * d) <= x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= 31624)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ¬((HasFactorBetween x_pre 2 d))) ,
  TT && emp 
|--
  “ (2 <= (d + 1)) ” &&
  “ ((d + 1) <= 31624) ” &&
  “ (2 <= x_pre) ” &&
  “ (x_pre <= 1000000000) ” &&
  “ ¬((HasFactorBetween x_pre 2 (d + 1))) ”
  &&  emp
) \/
(
forall (x_pre : Int) (d : Int) (PreH1 : ((Z.rem x_pre d) ≠ (0 : Int))) (PreH2 : ((d * d) <= x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= 31624)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ¬((HasFactorBetween x_pre 2 d))) ,
  TT && emp 
|--
  “ ¬((HasFactorBetween x_pre 2 (d + 1))) ”
  &&  emp
)

noncomputable def test_prime_sqrt_entail_wit_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (d : Int) (PreH1 : ((Z.rem x_pre d) ≠ (0 : Int))) (PreH2 : ((d * d) <= x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= 31624)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ¬((HasFactorBetween x_pre 2 d))) ,
  ¬((HasFactorBetween x_pre 2 (d + 1)))

noncomputable def test_prime_sqrt_return_wit_1 : Prop :=
  (
forall (x_pre : Int) (d : Int) (PreH1 : ((d * d) > x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= 31624)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ¬((HasFactorBetween x_pre 2 d))) ,
  TT && emp 
|--
  “ (1 = 1) ” &&
  “ (prime x_pre) ”
  &&  emp
) \/
(
forall (x_pre : Int) (d : Int) (PreH1 : ((d * d) > x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= 31624)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ¬((HasFactorBetween x_pre 2 d))) ,
  TT && emp 
|--
  “ (prime x_pre) ”
  &&  emp
)

noncomputable def test_prime_sqrt_return_wit_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (d : Int) (PreH1 : ((d * d) > x_pre)) (PreH2 : (2 <= d)) (PreH3 : (d <= 31624)) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 1000000000)) (PreH6 : ¬((HasFactorBetween x_pre 2 d))) ,
  (prime x_pre)

noncomputable def test_prime_sqrt_return_wit_2 : Prop :=
  (
forall (x_pre : Int) (d : Int) (PreH1 : ((Z.rem x_pre d) = (0 : Int))) (PreH2 : ((d * d) <= x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= 31624)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ¬((HasFactorBetween x_pre 2 d))) ,
  TT && emp 
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ¬((prime x_pre)) ”
  &&  emp
) \/
(
forall (x_pre : Int) (d : Int) (PreH1 : ((Z.rem x_pre d) = (0 : Int))) (PreH2 : ((d * d) <= x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= 31624)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ¬((HasFactorBetween x_pre 2 d))) ,
  TT && emp 
|--
  “ ¬((prime x_pre)) ”
  &&  emp
)

noncomputable def test_prime_sqrt_return_wit_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (d : Int) (PreH1 : ((Z.rem x_pre d) = (0 : Int))) (PreH2 : ((d * d) <= x_pre)) (PreH3 : (2 <= d)) (PreH4 : (d <= 31624)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 1000000000)) (PreH7 : ¬((HasFactorBetween x_pre 2 d))) ,
  ¬((prime x_pre))

noncomputable def test_prime_sqrt_return_wit_3 : Prop :=
  (
forall (x_pre : Int) (PreH1 : (x_pre < 2)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  TT && emp 
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ¬((prime x_pre)) ”
  &&  emp
) \/
(
forall (x_pre : Int) (PreH1 : (x_pre < 2)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  TT && emp 
|--
  “ ¬((prime x_pre)) ”
  &&  emp
)

noncomputable def test_prime_sqrt_return_wit_3_split_goal_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre < 2)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000)) ,
  ¬((prime x_pre))


structure VC_Correct : Type where
  proof_of_test_prime_safety_wit_1 : test_prime_safety_wit_1
  proof_of_test_prime_safety_wit_2 : test_prime_safety_wit_2
  proof_of_test_prime_safety_wit_3 : test_prime_safety_wit_3
  proof_of_test_prime_safety_wit_4 : test_prime_safety_wit_4
  proof_of_test_prime_safety_wit_5 : test_prime_safety_wit_5
  proof_of_test_prime_safety_wit_6 : test_prime_safety_wit_6
  proof_of_test_prime_safety_wit_7 : test_prime_safety_wit_7
  proof_of_test_prime_safety_wit_8 : test_prime_safety_wit_8
  proof_of_test_prime_sqrt_safety_wit_1 : test_prime_sqrt_safety_wit_1
  proof_of_test_prime_sqrt_safety_wit_2 : test_prime_sqrt_safety_wit_2
  proof_of_test_prime_sqrt_safety_wit_3 : test_prime_sqrt_safety_wit_3
  proof_of_test_prime_sqrt_safety_wit_4 : test_prime_sqrt_safety_wit_4
  proof_of_test_prime_sqrt_safety_wit_5 : test_prime_sqrt_safety_wit_5
  proof_of_test_prime_sqrt_safety_wit_6 : test_prime_sqrt_safety_wit_6
  proof_of_test_prime_sqrt_safety_wit_7 : test_prime_sqrt_safety_wit_7
  proof_of_test_prime_sqrt_safety_wit_8 : test_prime_sqrt_safety_wit_8
  proof_of_test_prime_sqrt_safety_wit_9 : test_prime_sqrt_safety_wit_9
  proof_of_test_prime_entail_wit_1 : test_prime_entail_wit_1
  proof_of_test_prime_entail_wit_2 : test_prime_entail_wit_2
  proof_of_test_prime_return_wit_1 : test_prime_return_wit_1
  proof_of_test_prime_return_wit_2 : test_prime_return_wit_2
  proof_of_test_prime_return_wit_3 : test_prime_return_wit_3
  proof_of_test_prime_sqrt_entail_wit_1 : test_prime_sqrt_entail_wit_1
  proof_of_test_prime_sqrt_entail_wit_2 : test_prime_sqrt_entail_wit_2
  proof_of_test_prime_sqrt_return_wit_1 : test_prime_sqrt_return_wit_1
  proof_of_test_prime_sqrt_return_wit_2 : test_prime_sqrt_return_wit_2
  proof_of_test_prime_sqrt_return_wit_3 : test_prime_sqrt_return_wit_3

end SimpleC.EE.QCP_demos_LLM.generated.test_prime_goal
