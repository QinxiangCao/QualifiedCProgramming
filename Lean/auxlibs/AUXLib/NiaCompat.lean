import Lean.Elab.Tactic.Omega

open Lean Meta Elab Tactic

namespace AUXLib.NiaCompat

theorem mul_le_of_nonneg_of_le_one_right {a b bound : Int}
    (ha : 0 <= a) (_hb : 0 <= b) (hb1 : b <= 1) (habound : a <= bound) :
    a * b <= bound := by
  have hmul : a * b <= a * 1 := Int.mul_le_mul_of_nonneg_left hb1 ha
  have hmul' : a * b <= a := by simpa using hmul
  exact Int.le_trans hmul' habound

theorem mul_le_of_nonneg_of_le_one_left {a b bound : Int}
    (ha : 0 <= a) (ha1 : a <= 1) (hb : 0 <= b) (hbbound : b <= bound) :
    a * b <= bound := by
  rw [Int.mul_comm]
  exact mul_le_of_nonneg_of_le_one_right hb ha ha1 hbbound

theorem square_le_mul_of_le {d q n : Int}
    (hd : 0 <= d) (hdq : d <= q) (hdn : d <= n) : d * d <= q * n := by
  exact Int.mul_le_mul hdq hdn hd (Int.le_trans hd hdq)

theorem mul_nonpos_of_nonpos_of_nonneg {a b : Int}
    (ha : a <= 0) (hb : 0 <= b) : a * b <= 0 := by
  exact Int.mul_nonpos_of_nonpos_of_nonneg ha hb

theorem square_nonneg (a : Int) : 0 <= a * a := by
  by_cases ha : 0 <= a
  · exact Int.mul_nonneg ha ha
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

theorem decomposition_lt {square value delta0 delta1 delta2 d : Int}
    (hzero : delta0 = square) (hvalue : delta2 = value)
    (hdecomp : delta0 = delta1 + (4 - d) * delta2)
    (hdelta : delta2 > delta1) (hd : 0 < d) (hpositive : 0 < value) :
    square - 4 * value < 0 := by
  have hdeltaNonneg : 0 <= delta2 := by
    rw [hvalue]
    omega
  have hprod : delta2 <= d * delta2 := by
    have h := Int.mul_le_mul_of_nonneg_right (show (1 : Int) <= d by omega)
      hdeltaNonneg
    simpa using h
  rw [← hzero, hdecomp, ← hvalue, Int.sub_mul]
  omega

theorem succ_le_of_square_bound {d x upper : Int}
    (hsquare : d * d <= x) (hupper : 0 <= upper)
    (hx : x < upper * upper) :
    d + 1 <= upper := by
  by_cases hsucc : d + 1 <= upper
  · exact hsucc
  · have hud : upper <= d := by omega
    have hm : upper * upper <= d * d :=
      Int.mul_le_mul hud hud hupper (Int.le_trans hupper hud)
    omega

theorem lt_of_self_mul_le {d x : Int}
    (hsquare : d * d <= x) (hd : 2 <= d) :
    d < x := by
  have hmul : d < d * d := by
    have h := Int.mul_lt_mul_of_pos_right (show (1 : Int) < d by omega)
      (show 0 < d by omega)
    simpa using h
  omega

private def intLocalFVars : MetaM (List FVarId) := do
  let mut result := []
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let saved ← saveState
      let isInt ← withTransparency .reducible <|
        isDefEq localDecl.type (mkConst ``Int)
      restoreState saved
      if isInt then
        result := localDecl.fvarId :: result
  return result.reverse

private def tryOmegaProof (type : Expr) : TacticM (Option Expr) := do
  let saved ← saveState
  let savedGoals ← getGoals
  try
    let proof ← mkFreshExprSyntheticOpaqueMVar type
    setGoals [proof.mvarId!]
    evalTactic (← `(tactic| omega))
    unless (← getGoals).isEmpty do
      throwError "omega left residual goals"
    let proof ← instantiateMVars proof
    setGoals savedGoals
    return some proof
  catch _ =>
    restoreState saved
    return none

private def assertFact (name : Name) (type proof : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  let asserted ← goal.assert name type proof
  let (_, next) ← asserted.intro1P
  replaceMainGoal [next]

private partial def containsMultiplication : Expr -> Bool
  | .const name _ => name == ``HMul.hMul || name == ``Int.mul
  | .app function argument =>
      containsMultiplication function || containsMultiplication argument
  | .lam _ domain body _ | .forallE _ domain body _ =>
      containsMultiplication domain || containsMultiplication body
  | .letE _ type value body _ =>
      containsMultiplication type || containsMultiplication value ||
        containsMultiplication body
  | .mdata _ body | .proj _ _ body => containsMultiplication body
  | _ => false

private def isIntType (type : Expr) : MetaM Bool := do
  let saved <- saveState
  let result <- withTransparency .reducible <| isDefEq type (mkConst ``Int)
  restoreState saved
  return result

private partial def isArithmeticTarget (target : Expr) : MetaM Bool := do
  if target.isAppOfArity ``Not 1 then
    return <- isArithmeticTarget target.appArg!
  if target.isConstOf ``False then
    return true
  let function := target.getAppFn
  if function.isConstOf ``Int.le || function.isConstOf ``Int.lt ||
      function.isConstOf ``LE.le || function.isConstOf ``LT.lt then
    return true
  if function.isConstOf ``Eq then
    let arguments := target.getAppArgs
    if h : 0 < arguments.size then
      if arguments[0].isConstOf ``Int then
        return true
      return <- isIntType arguments[0]
    else
      return false
  let target <- whnf target
  let function := target.getAppFn
  if function.isConstOf ``Int.NonNeg then
    return true
  if function.isConstOf ``Eq then
    let arguments := target.getAppArgs
    if h : 0 < arguments.size then
      if arguments[0].isConstOf ``Int then
        return true
      return <- isIntType arguments[0]
  return false

private def guardMultiplication : TacticM Unit := withMainContext do
  let goal <- getMainGoal
  let target <- instantiateMVars (← goal.getType)
  unless <- isArithmeticTarget target do
    throwError "nia target is not a supported integer relation"
  if containsMultiplication target then
    return
  for localDecl in <- getLCtx do
    unless localDecl.isImplementationDetail do
      if containsMultiplication (← instantiateMVars localDecl.type) then
        return
  throwError "nia found no nonlinear multiplication"

private def addPositiveProductFacts : TacticM Unit := do
  let fvars ← intLocalFVars
  let zero := mkApp (mkConst ``Int.ofNat) (mkNatLit 0)
  let one := mkApp (mkConst ``Int.ofNat) (mkNatLit 1)
  for leftId in fvars do
    for rightId in fvars do
      withMainContext do
        let left := mkFVar leftId
        let right := mkFVar rightId
        let leftPosType := mkApp2 (mkConst ``Int.lt) zero left
        let rightPosType := mkApp2 (mkConst ``Int.lt) zero right
        if let some leftPos ← tryOmegaProof leftPosType then
          if let some rightPos ← tryOmegaProof rightPosType then
            let proof ← mkAppM ``Int.mul_pos #[leftPos, rightPos]
            assertFact `_nia_mul_pos (← inferType proof) proof
        let leftOneType := mkApp2 (mkConst ``Int.le) one left
        let rightNonnegType := mkApp2 (mkConst ``Int.le) zero right
        if let some leftOne ← tryOmegaProof leftOneType then
          if let some rightNonneg ← tryOmegaProof rightNonnegType then
            let proof ← mkAppM ``Int.mul_le_mul_of_nonneg_right
              #[leftOne, rightNonneg]
            assertFact `_nia_mul_ge_right (← inferType proof) proof

end AUXLib.NiaCompat

syntax "nia" : tactic
syntax "_nia_core" : tactic
syntax "_nia_add_positive_products" : tactic
syntax "_nia_guard_multiplication" : tactic

elab_rules : tactic
  | `(tactic| _nia_add_positive_products) =>
      AUXLib.NiaCompat.addPositiveProductFacts
  | `(tactic| _nia_guard_multiplication) =>
      AUXLib.NiaCompat.guardMultiplication
  | `(tactic| nia) => do
      let saved <- saveState
      let goals <- getGoals
      let mainGoal :: remainingGoals := goals
        | throwError "no goals to be solved"
      setGoals [mainGoal]
      try
        evalTactic (← `(tactic| _nia_core))
        let generatedGoals <- getGoals
        setGoals (generatedGoals ++ remainingGoals)
      catch error =>
        restoreState saved
        throw error

macro_rules
  | `(tactic| _nia_core) => `(tactic|
      first
      | omega
      | (_nia_guard_multiplication;
          first
          | (simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] <;> omega)
          | (simp_all only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub,
              Int.mul_assoc] <;> omega)
          | (_nia_add_positive_products;
              simp_all only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub,
                Int.mul_assoc] <;> omega)
          | (apply AUXLib.NiaCompat.square_nonneg)
          | (simp only [Int.mul_assoc];
              apply AUXLib.NiaCompat.decomposition_lt <;> first | assumption | rfl)
          | (apply Int.mul_le_mul_of_nonneg_left <;> omega)
          | (apply Int.mul_le_mul_of_nonneg_right <;> omega)
          | (apply AUXLib.NiaCompat.mul_nonpos_of_nonpos_of_nonneg <;> omega)
          | (apply Int.mul_nonpos_of_nonneg_of_nonpos <;> omega)
          | (apply AUXLib.NiaCompat.square_le_mul_of_le <;> omega)
          | (apply AUXLib.NiaCompat.succ_le_of_square_bound <;>
              first | assumption | omega)
          | (apply AUXLib.NiaCompat.lt_of_self_mul_le <;>
              first | assumption | omega)
          | (apply AUXLib.NiaCompat.mul_le_of_nonneg_of_le_one_right <;> omega)
          | (apply AUXLib.NiaCompat.mul_le_of_nonneg_of_le_one_left <;> omega)))
