import Unifysl.GeneralLogic.ProofTheory.ProofTheoryPatternsD1
import Unifysl.MinimumLogic.ProofTheory.ProofTheoryPatternsP

/-!
Coq inventory from `MinimumLogic/ProofTheory/ProofTheoryPatterns.v`:
- Requires:
  `Logic.GeneralLogic.ProofTheory.ProofTheoryPatternsD1`,
  `Logic.MinimumLogic.ProofTheory.ProofTheoryPatternsP`.
- Module aliases:
  `Module D1 := ProofTheoryPatternsD1.`
  `Module P := ProofTheoryPatternsP.`
-/

namespace Unifysl

namespace ProofTheoryPatterns

namespace D1

export Unifysl (
  Adjointness
  Commutativity
  Monotonicity
  Associativity
  LeftUnit
  RightUnit
  LeftDistr
  RightDistr
  adjoint
  derivable1_prodp_comm
  prodp_mono
  prodp_assoc1
  prodp_assoc2
  left_unit1
  left_unit2
  right_unit1
  right_unit2
  left_distr1
  left_distr2
  right_distr1
  right_distr2
  prodp_mono1
  funcp_mono2
  adjoint_modus_ponens
  adjoint_iter
  Adjoint2Mono
  funcp_mono
  fold_left_mono
  fold_right_mono
  fold_left_mono2
  fold_right_mono2
  assoc_fold_left_cons
  assoc_fold_right_cons
  assoc_fold_left_fold_right
  assoc_fold_right_fold_left
  assoc_prodp_fold_left
  assoc_fold_left_app
  LeftDistr2RightDistr
  RightDistr2LeftDistr
  Build_Associativity1
  Build_Associativity2
)

end D1

namespace P

export Unifysl.ProofTheoryPatternsP (
  Adjointness
  Commutativity
  Monotonicity
  Associativity
  LeftUnit
  RightUnit
  LeftDistr
  RightDistr
  adjoint
  prodp_comm_impp
  prodp_mono
  prodp_assoc1
  prodp_assoc2
  left_unit1
  left_unit2
  right_unit1
  right_unit2
  left_distr1
  left_distr2
  right_distr1
  right_distr2
  prodp_mono1
  funcp_mono2
  adjoint_modus_ponens
  adjoint_iter
  Adjoint2Mono
  funcp_mono
  fold_left_mono
  fold_right_mono
  fold_left_mono2
  fold_right_mono2
  assoc_fold_left_cons
  assoc_fold_right_cons
  assoc_fold_left_fold_right
  assoc_fold_right_fold_left
  assoc_prodp_fold_left
  assoc_fold_left_app
  LeftDistr2RightDistr
  RightDistr2LeftDistr
  Build_Associativity1
  Build_Associativity2
)

end P

end ProofTheoryPatterns

end Unifysl
