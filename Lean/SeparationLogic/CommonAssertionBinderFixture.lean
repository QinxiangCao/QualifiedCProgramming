import SimpleC.SL.CommonAssertion

namespace CommonAssertionBinderFixture

open SimpleC.SL.CommonAssertion

def namedBinderGoal (CRules : SeparationLogicSig) : Prop :=
  forall sourceAssertion : CRules.expr,
    CRules.derivable1 sourceAssertion
      (CRules.exp Int fun _ => sourceAssertion)

end CommonAssertionBinderFixture
