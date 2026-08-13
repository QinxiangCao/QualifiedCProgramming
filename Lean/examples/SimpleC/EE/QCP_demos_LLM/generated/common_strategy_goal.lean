import SimpleC.SL.SeparationLogic

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC


local instance commonStrategyGoalSacContext : SacContext := { CRules := naive_C_Rules }


noncomputable def common_strategy0 : Prop :=
  forall (A : Type) (x : A),
    TT &&
    (“ (x = x) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    )

noncomputable def common_strategy1 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL A : Type, ALL x : A, 
    TT &&
    emp -*
    TT &&
    (“ (x = x) ”) &&
    emp
    )

noncomputable def common_strategy6 : Prop :=
  forall ty (y : Int) (x : Int) (p : Int),
    TT &&
    emp **
    ((p # ty |-> (x)))
    |--
    (
    TT &&
    (“ (should_be_equal x y) ”) &&
    emp **
    ((p # ty |-> (x)))
    ) ** (
    TT &&
    (“ (x = y) ”) &&
    emp **
    ((p # ty |-> (y))) -*
    TT &&
    emp **
    ((p # ty |-> (y)))
    )

noncomputable def common_strategy19 : Prop :=
  forall (x : Int) (p : Int),
    TT &&
    emp **
    ((p # INT |-> (x)))
    |--
    (
    TT &&
    (“ (x >= (INT_MIN)) ”) &&
    emp **
    ((p # INT |-> (x)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    )

noncomputable def common_strategy20 : Prop :=
  forall (x : Int) (p : Int),
    TT &&
    emp **
    ((p # INT |-> (x)))
    |--
    (
    TT &&
    (“ (x <= (INT_MAX)) ”) &&
    emp **
    ((p # INT |-> (x)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    )

noncomputable def common_strategy21 : Prop :=
  forall (x : Int) (p : Int),
    TT &&
    emp **
    ((p # UINT |-> (x)))
    |--
    (
    TT &&
    (“ (x >= (0 : Int)) ”) &&
    emp **
    ((p # UINT |-> (x)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    )

noncomputable def common_strategy22 : Prop :=
  forall (x : Int) (p : Int),
    TT &&
    emp **
    ((p # UINT |-> (x)))
    |--
    (
    TT &&
    (“ (x <= (UINT_MAX)) ”) &&
    emp **
    ((p # UINT |-> (x)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    )

noncomputable def common_strategy3 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL A : Type, ALL y : A, ALL x : A, 
    TT &&
    (“ (x = y) ” || “ (y = x) ”) &&
    emp -*
    TT &&
    (“ (x = y) ” || “ (y = x) ”) &&
    emp
    )

noncomputable def common_strategy15 : Prop :=
  forall ty ty1 (x : Int) (y : Int) (p : Int),
    TT &&
    emp **
    ((p # ty |-> (x))) **
    ((p # ty1 |-> (y)))
    |--
    (
    TT &&
    (“ (dup_data_at_error_prop SacContext.rules) ”) &&
    emp **
    ((p # ty |-> (x))) **
    ((p # ty1 |-> (y)))
    ) ** (
    TT &&
    emp **
    ((dup_data_at_error SacContext.rules p)) -*
    TT &&
    emp
    )

noncomputable def common_strategy16 : Prop :=
  forall ty ty1 (x : Int) (p : Int),
    TT &&
    emp **
    ((p # ty |-> (x))) **
    ((p # ty1 |->_))
    |--
    (
    TT &&
    (“ (dup_data_at_error_prop SacContext.rules) ”) &&
    emp **
    ((p # ty |-> (x))) **
    ((p # ty1 |->_))
    ) ** (
    TT &&
    emp **
    ((dup_data_at_error SacContext.rules p)) -*
    TT &&
    emp
    )

noncomputable def common_strategy17 : Prop :=
  forall ty ty1 (p : Int),
    TT &&
    emp **
    ((p # ty |->_)) **
    ((p # ty1 |->_))
    |--
    (
    TT &&
    (“ (dup_data_at_error_prop SacContext.rules) ”) &&
    emp **
    ((p # ty |->_)) **
    ((p # ty1 |->_))
    ) ** (
    TT &&
    emp **
    ((dup_data_at_error SacContext.rules p)) -*
    TT &&
    emp
    )

noncomputable def common_strategy12 : Prop :=
  forall (A : Type) (b : A) (a : A),
    TT &&
    (“ (should_be_equal a b) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    )

noncomputable def common_strategy13 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL A : Type, ALL b : A, ALL a : A, 
    TT &&
    emp -*
    TT &&
    (“ (should_be_equal a b) ”) &&
    emp
    )

noncomputable def common_strategy18 : Prop :=
  TT &&
  (“ (dup_data_at_error_prop SacContext.rules) ”) &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  )

noncomputable def common_strategy7 : Prop :=
  forall ty (x : Int) (p : Int),
    TT &&
    emp **
    ((p # ty |-> (x)))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((p # ty |-> (x)))
    )

noncomputable def common_strategy8 : Prop :=
  forall ty (x : Int) (p : Int),
    TT &&
    emp **
    ((p # ty |-> (x)))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL y : Int, 
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      (“ (x = y) ”) &&
      emp **
      ((p # ty |-> (y)))
      )

noncomputable def common_strategy9 : Prop :=
  forall ty (x : Int) (p : Int),
    TT &&
    emp **
    ((p # ty |-> (x)))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((p # ty |->_))
    )

noncomputable def common_strategy10 : Prop :=
  forall ty (p : Int),
    TT &&
    emp **
    ((p # ty |->_))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((p # ty |->_))
    )

noncomputable def common_strategy11 : Prop :=
  forall ty (q : Int) (p : Int) (x : Int),
    TT &&
    (“ (p = q) ” || “ (q = p) ”) &&
    emp **
    ((p # ty |-> (x)))
    |--
    (
    TT &&
    (“ (p = q) ” || “ (q = p) ”) &&
    emp
    ) ** (
    ALL y : Int, 
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      emp **
      ((q # ty |-> (y)))
      )

noncomputable def common_strategy23 : Prop :=
  forall (n : Int),
    TT &&
    (“ (n > (0 : Int)) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL x : Int, 
      TT &&
      emp -*
      TT &&
      (“ ((unsigned_last_nbits x n) >= (0 : Int)) ”) &&
      emp
      )

noncomputable def common_strategy14 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL ty, ALL x : Int, ALL p : Int, 
    TT &&
    emp **
    ((p # ty |-> (x))) -*
    TT &&
    emp **
    ((p # ty |->_))
    )

structure common_Strategy_Correct : Type where
  common_strategy0_correctness : common_strategy0
  common_strategy1_correctness : common_strategy1
  common_strategy6_correctness : common_strategy6
  common_strategy19_correctness : common_strategy19
  common_strategy20_correctness : common_strategy20
  common_strategy21_correctness : common_strategy21
  common_strategy22_correctness : common_strategy22
  common_strategy3_correctness : common_strategy3
  common_strategy15_correctness : common_strategy15
  common_strategy16_correctness : common_strategy16
  common_strategy17_correctness : common_strategy17
  common_strategy12_correctness : common_strategy12
  common_strategy13_correctness : common_strategy13
  common_strategy18_correctness : common_strategy18
  common_strategy7_correctness : common_strategy7
  common_strategy8_correctness : common_strategy8
  common_strategy9_correctness : common_strategy9
  common_strategy10_correctness : common_strategy10
  common_strategy11_correctness : common_strategy11
  common_strategy23_correctness : common_strategy23
  common_strategy14_correctness : common_strategy14

end SimpleC.EE.QCP_demos_LLM.generated.common_strategy_goal
