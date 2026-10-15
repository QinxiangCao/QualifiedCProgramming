import SimpleC.SL.SeparationLogic
import MaxMinLib.Interface
import ListLib.General.NoDup
import ListLib.General.Forall
import ListLib.General.Presuffix
import ListLib.General.IndexedElements
import Lean.Util.CollectAxioms

-- SeparationLogic brings Mathlib through FloatLib. These imports exercise the
-- MaxMin namespace compatibility in the same environment used by the examples.
#check MaxMinLib.max_value_of_subset
#check MaxMinLib.min_value_of_subset
#check MaxMinLib.max_n_in_range
#check MaxMinLib.Z_op_finite_min
#check SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full
#check SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.mixed_full
#check SimpleC.SL.SeparationLogic.naive_C_Rules.CharArray2.full
#check Real

run_cmd do
  for decl in #[``MaxMinLib.max_n_in_range, ``MaxMinLib.Z_op_finite_min] do
    if (← Lean.collectAxioms decl).contains ``sorryAx then
      throwError "Upstream MaxMin theorem {decl} depends on sorryAx"
