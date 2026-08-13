import compcert.lib.Integers
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Cases

namespace AUXLib

open Lean Meta Elab Tactic

theorem min_signed_lt0 : Int64.min_signed < 0 := by decide

theorem max_signed_gt0 : Int64.max_signed > 0 := by decide

theorem zdiv_equiv (x y : Int) (hx : x >= 0) (hy : y > 0) :
    Z.quot x y = Z.div x y := by
  rw [Zbits.Zquot_Zdiv x y hy]
  simp [show ¬x < 0 by omega]

theorem zadd_rm_head (n p q : Int) (h : p = q) : n + p = n + q := by
  rw [h]

theorem zadd_rm_tail (n p q : Int) (h : p = q) : p + n = q + n := by
  rw [h]

theorem zdiv_range_le_lt (a b c x : Int)
    (ha : a <= 0) (hb : b > 0) (hc : c > 0) (hx : a <= x ∧ x < b) :
    a <= Z.div x c ∧ Z.div x c < b := by
  unfold Z.div
  rw [Int.fdiv_eq_ediv_of_nonneg x (by omega)]
  have hac : a * c <= a := by
    calc
      a * c = a + a * (c - 1) := by grind
      _ <= a + 0 := Int.add_le_add_left
        (Int.mul_nonpos_of_nonpos_of_nonneg ha (by omega)) a
      _ = a := by simp
  have hbc : b <= b * c := by
    calc
      b = b + 0 := by simp
      _ <= b + b * (c - 1) := Int.add_le_add_left
        (Int.mul_nonneg (by omega) (by omega)) b
      _ = b * c := by grind
  constructor
  · exact Int.le_ediv_of_mul_le hc (by omega)
  · exact Int.ediv_lt_of_lt_mul hc (by omega)

theorem zdiv_range_le_le (a b c x : Int)
    (ha : a <= 0) (hb : b > 0) (hc : c > 0) (hx : a <= x ∧ x <= b) :
    a <= Z.div x c ∧ Z.div x c <= b := by
  unfold Z.div
  rw [Int.fdiv_eq_ediv_of_nonneg x (by omega)]
  have hac : a * c <= a := by
    calc
      a * c = a + a * (c - 1) := by grind
      _ <= a + 0 := Int.add_le_add_left
        (Int.mul_nonpos_of_nonpos_of_nonneg ha (by omega)) a
      _ = a := by simp
  have hbc : b <= b * c := by
    calc
      b = b + 0 := by simp
      _ <= b + b * (c - 1) := Int.add_le_add_left
        (Int.mul_nonneg (by omega) (by omega)) b
      _ = b * c := by grind
  constructor
  · exact Int.le_ediv_of_mul_le hc (by omega)
  · exact Int.ediv_le_of_le_mul hc (by omega)

theorem max_unsigned_gt0 : Int64.max_unsigned > 0 := by decide

theorem max_unsigned_val : Int64.max_unsigned = 18446744073709551615 := rfl

theorem max_signed_val : Int64.max_signed = 9223372036854775807 := rfl

theorem min_signed_val : Int64.min_signed = -9223372036854775808 := rfl

theorem unsigned_mone_val :
    Int64.unsigned Int64.mone = 18446744073709551615 := by native_decide

theorem modulus_val : Int64.modulus = 18446744073709551616 := rfl

theorem unsigned_inj (a b : Int64.int)
    (h : Int64.unsigned a = Int64.unsigned b) : a = b := by
  exact CompCert.Int64.int.ext h

theorem minus1lt (i : Int) : i - 1 < i := by omega

theorem Z_land_range_lo (x y : Int) (hx : 0 <= x) : 0 <= Z.land x y := by
  cases x with
  | negSucc x => omega
  | ofNat x => cases y <;> simp [Z.land]

theorem Z_land_range_lo_r (x y : Int) (hy : 0 <= y) : 0 <= Z.land x y := by
  rw [Z.land_comm]
  exact Z_land_range_lo y x hy

theorem unsigned_zero : Int64.unsigned Int64.zero = 0 := Int64.unsigned_zero
theorem unsigned_one : Int64.unsigned Int64.one = 1 := Int64.unsigned_one
theorem eq_one_zero : Int64.eq Int64.one Int64.zero = false := by native_decide
theorem eq_zero_zero : Int64.eq Int64.zero Int64.zero = true := by native_decide
theorem negb_true : (!true) = false := rfl
theorem negb_false : (!false) = true := rfl
theorem repr_zero : Int64.repr 0 = Int64.zero := rfl
theorem repr_one : Int64.repr 1 = Int64.one := rfl
theorem and_zero_zero : Z.land 0 0 = 0 := rfl
theorem and_one_zero : Z.land 1 0 = 0 := rfl
theorem and_zero_one : Z.land 0 1 = 0 := rfl
theorem and_one_one : Z.land 1 1 = 1 := rfl
theorem or_zero_zero : Z.lor 0 0 = 0 := rfl
theorem or_one_zero : Z.lor 1 0 = 1 := rfl
theorem or_zero_one : Z.lor 0 1 = 1 := rfl
theorem or_one_one : Z.lor 1 1 = 1 := rfl

private theorem repr_eq_word_unsigned (z : Int) (i : Int64.int)
    (h : z = CompCert.Int64.unsigned i) : CompCert.Int64.repr z = i := by
  rw [h, CompCert.Int64.repr_unsigned]

private theorem word_eq_repr_unsigned (i : Int64.int) (z : Int)
    (h : CompCert.Int64.unsigned i = z) : i = CompCert.Int64.repr z := by
  rw [← CompCert.Int64.repr_unsigned i, h]

private structure IntAutoRangeWords where
  signed : Array Expr := #[]
  unsigned : Array Expr := #[]

private def observedWord? (root : Expr) (signed : Bool) : Option Expr :=
  (root.find? fun e =>
    let fnName := match e.getAppFn with
      | .const name _ => name
      | _ => Name.anonymous
    if signed then
      fnName == ``Int64.signed || fnName == ``CompCert.Int64.signed
    else
      fnName == ``Int64.unsigned || fnName == ``CompCert.Int64.unsigned).bind
    (fun e => e.getAppArgs.back?)

private def collectIntAutoWords (roots : Array Expr) : MetaM IntAutoRangeWords := do
  let signedRef ← IO.mkRef (#[] : Array Expr)
  let unsignedRef ← IO.mkRef (#[] : Array Expr)
  let addWord (wordsRef : IO.Ref (Array Expr)) (word : Expr) : MetaM Unit := do
    let words ← wordsRef.get
    unless words.any fun old => old == word do
      wordsRef.set (words.push word)
  let mut pending := roots.toList
  while !pending.isEmpty do
    match pending with
    | [] => pure ()
    | root :: rest =>
        let root := root.consumeMData
        pending := rest
        let fnName := match root.getAppFn with
          | .const name _ => name
          | _ => Name.anonymous
        let isArithmetic := fnName == ``HAdd.hAdd || fnName == ``HSub.hSub ||
          fnName == ``HMul.hMul || fnName == ``HDiv.hDiv || fnName == ``Z.div
        let args := root.getAppArgs
        if isArithmetic && args.size >= 2 then
          if let some left := args[args.size - 2]? then
            if let some right := args[args.size - 1]? then
              pending := left :: right :: pending
        else if let some word := observedWord? root true then
          addWord signedRef word
        else if let some word := observedWord? root false then
          addWord unsignedRef word
  return { signed := ← signedRef.get, unsigned := ← unsignedRef.get }

private def assertIntAutoRanges (words : IntAutoRangeWords) : TacticM Unit := do
  let goal ← getMainGoal
  let mut hypotheses : Array Hypothesis := #[]
  let mut generatedNames : Array Name := #[]
  for word in words.signed do
    let signedProof ← mkAppM ``CompCert.Int64.signed_range #[word]
    let userName ← mkFreshUserName `signed_range
    generatedNames := generatedNames.push userName
    hypotheses := hypotheses.push {
      userName
      type := ← inferType signedProof
      value := signedProof
      binderInfo := BinderInfo.default
      kind := LocalDeclKind.default }
  for word in words.unsigned do
    let unsignedProof ← mkAppM ``CompCert.Int64.unsigned_range #[word]
    let userName ← mkFreshUserName `unsigned_range
    generatedNames := generatedNames.push userName
    hypotheses := hypotheses.push {
      userName
      type := ← inferType unsignedProof
      value := unsignedProof
      binderInfo := BinderInfo.default
      kind := LocalDeclKind.default }
  unless hypotheses.isEmpty do
    let (_, nextGoal) ← goal.assertHypotheses hypotheses
    replaceMainGoal [nextGoal]
    for userName in generatedNames do
      let hypothesis := mkIdent userName
      evalTactic (← `(tactic|
        try simp only [min_signed_val, max_signed_val, max_unsigned_val,
          modulus_val] at $hypothesis:ident))

private def addIntAutoRangesFromTarget : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let fnName := match target.getAppFn with
    | .const name _ => name
    | _ => Name.anonymous
  let args := target.getAppArgs
  let roots := if (fnName == ``LE.le || fnName == ``LT.lt) && args.size >= 2 then
      #[args[args.size - 2]!, args[args.size - 1]!]
    else
      #[target]
  assertIntAutoRanges (← collectIntAutoWords roots)

private def addIntAutoRangesFromTerm (term : Syntax) : TacticM Unit := withMainContext do
  let expression ← Lean.Elab.Term.elabTerm term none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  assertIntAutoRanges (← collectIntAutoWords #[← instantiateMVars expression])

private def isSelectedOperation (expression : Expr) (division : Bool) : MetaM Bool := do
  let name ← match expression.getAppFn with
    | .const name _ => pure name
    | _ => pure Name.anonymous
  let selected := if division then
      name == ``Z.div
    else
      name == ``HMul.hMul
  if !selected then
    return false
  unless ← isDefEq (← inferType expression) (mkConst ``Int) do
    return false
  if !division then
    let args := expression.getAppArgs
    unless args.size ≥ 3 do
      return false
    let multiplicationInstance := args[args.size - 3]!
    if multiplicationInstance.hasFVar || multiplicationInstance.hasMVar then
      return false
    unless multiplicationInstance.getAppFn.isConstOf ``instHMul do
      return false
    let instanceArgs := multiplicationInstance.getAppArgs
    unless instanceArgs.size ≥ 1 &&
        instanceArgs[instanceArgs.size - 1]!.isConstOf ``Int.instMul do
      return false
    let lhs := args[args.size - 2]!
    let rhs := args[args.size - 1]!
    return (← isDefEq (← inferType lhs) (mkConst ``Int)) &&
      (← isDefEq (← inferType rhs) (mkConst ``Int))
  return true

private def normalizeComputedInt (expression : Expr) : MetaM Expr := do
  let expression ← whnf expression
  if expression.isAppOfArity ``Int.ofNat 1 then
    if let some value ← (evalNat expression.appArg!).run then
      return mkIntLit (Int.ofNat value)
  if expression.isAppOfArity ``Int.negSucc 1 then
    if let some value ← (evalNat expression.appArg!).run then
      return mkIntLit (Int.negSucc value)
  return expression

private def evaluateSelectedOperation (expression : Expr) (division : Bool) :
    MetaM (Option Expr) := do
  let args := expression.getAppArgs
  unless args.size ≥ 2 do
    return none
  let lhs ← reduce args[args.size - 2]!
  let rhs ← reduce args[args.size - 1]!
  let some lhsValue ← getIntValue? lhs | return none
  let some rhsValue ← getIntValue? rhs | return none
  return some (mkIntLit (if division then
    Int.fdiv lhsValue rhsValue
  else
    lhsValue * rhsValue))

private partial def reduceFirstOperation (expression : Expr) (division : Bool) :
    MetaM (Option Expr) := do
  if ← isSelectedOperation expression division then
    if expression.hasFVar || expression.hasMVar then
      return some expression
    if let some value ← evaluateSelectedOperation expression division then
      return some value
    return some (← normalizeComputedInt (← reduce expression))
  match expression with
  | .app fn argument =>
      if let some fn' ← reduceFirstOperation fn division then
        return some (.app fn' argument)
      if let some argument' ← reduceFirstOperation argument division then
        return some (.app fn argument')
      return none
  | .lam name domain body binderInfo =>
      if let some domain' ← reduceFirstOperation domain division then
        return some (.lam name domain' body binderInfo)
      return (← reduceFirstOperation body division).map
        (fun body' => .lam name domain body' binderInfo)
  | .forallE name domain body binderInfo =>
      if let some domain' ← reduceFirstOperation domain division then
        return some (.forallE name domain' body binderInfo)
      return (← reduceFirstOperation body division).map
        (fun body' => .forallE name domain body' binderInfo)
  | .letE name type value body nondep =>
      if let some type' ← reduceFirstOperation type division then
        return some (.letE name type' value body nondep)
      if let some value' ← reduceFirstOperation value division then
        return some (.letE name type value' body nondep)
      return (← reduceFirstOperation body division).map
        (fun body' => .letE name type value body' nondep)
  | .mdata data body =>
      return (← reduceFirstOperation body division).map (fun body' => .mdata data body')
  | .proj typeName index body =>
      return (← reduceFirstOperation body division).map
        (fun body' => .proj typeName index body')
  | _ => return none

private def hasAndHypothesis : TacticM Bool := withMainContext do
  for localDecl in (← getLCtx) do
    unless localDecl.isImplementationDetail do
      let type ← instantiateMVars localDecl.type
      if type.isAppOfArity ``And 2 then
        return true
  return false

private def targetIsInequality : TacticM Bool := withMainContext do
  let target := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  let fnName := match target.getAppFn with
    | .const name _ => name
    | _ => Name.anonymous
  return fnName == ``LE.le || fnName == ``LT.lt

private partial def runSolveIntUnequal : TacticM Unit := do
  let hasAnd ← hasAndHypothesis
  let isInequality ← targetIsInequality
  if hasAnd then
    replaceMainGoal [← (← getMainGoal).casesAnd]
    runSolveIntUnequal
  else
    let target := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
    if target.isAppOfArity ``And 2 then
      evalTactic (← `(tactic| constructor))
      let branches ← getGoals
      let mut remaining : List MVarId := []
      for branch in branches do
        replaceMainGoal [branch]
        runSolveIntUnequal
        remaining := remaining ++ (← getGoals)
      setGoals remaining
    else if isInequality then
      addIntAutoRangesFromTarget
      unless (← getGoals).isEmpty do
        try
          evalTactic (← `(tactic|
            try simp (discharger :=
              try simp only [CompCert.Int64.min_signed_val,
                CompCert.Int64.max_signed_val, CompCert.Int64.max_unsigned_val,
                CompCert.Int64.modulus_val]
              omega) only [CompCert.Int64.signed_repr,
                CompCert.Int64.unsigned_repr] at *))
        catch _ => pure ()
      unless (← getGoals).isEmpty do
        evalTactic (← `(tactic|
          try simp only [Int64.signed, Int64.unsigned,
            min_signed_val, max_signed_val,
            max_unsigned_val, modulus_val] at *))
      unless (← getGoals).isEmpty do
        evalTactic (← `(tactic| try omega))

private def simplifyZdivHypotheses : TacticM Unit := withMainContext do
  let mut localDecls : Array LocalDecl := #[]
  for localDecl in (← getLCtx) do
    localDecls := localDecls.push localDecl
  for localDecl in localDecls do
    unless localDecl.isImplementationDetail do
      let type ← instantiateMVars localDecl.type
      if (type.find? fun expression =>
          expression.getAppFn.isConstOf ``Z.quot).isSome then
        let hypothesis := mkIdent localDecl.userName
        evalTactic (← `(tactic|
          try simp (discharger := first | assumption | omega) only
            [zdiv_equiv] at $hypothesis:ident))

private def runIntAutoSimpl : TacticM Unit := do
  replaceMainGoal [← (← getMainGoal).casesAnd]
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic|
      try simp only [CompCert.Int64.sub_add_cancel,
        CompCert.Int64.repr_signed, CompCert.Int64.repr_unsigned,
        CompCert.Int64.and_zero, CompCert.Int64.and_zero_l] at *))
    unless (← getGoals).isEmpty do
      evalTactic (← `(tactic|
        try simp (discharger :=
          try simp only [CompCert.Int64.min_signed_val,
            CompCert.Int64.max_signed_val, CompCert.Int64.max_unsigned_val,
            CompCert.Int64.modulus_val]
          omega) only [unsigned_zero, unsigned_one, unsigned_mone_val,
            CompCert.Int64.signed_zero, CompCert.Int64.signed_one,
            CompCert.Int64.signed_mone, eq_one_zero, eq_zero_zero,
            Int64.eq_true, decide_eq_true_eq, decide_eq_false_iff_not,
            negb_true, negb_false, repr_zero, repr_one,
            CompCert.Int64.repr_signed, CompCert.Int64.repr_unsigned,
            CompCert.Int64.signed_repr, CompCert.Int64.unsigned_repr,
            CompCert.Int64.and_zero, Int64.and_zero_l,
            CompCert.Int64.sub_add_cancel, min_signed_val, max_signed_val,
            max_unsigned_val, modulus_val, and_zero_zero, and_zero_one,
            and_one_zero, and_one_one, or_zero_zero, or_zero_one,
            or_one_zero, or_one_one, CompCert.Int64.cmpu, CompCert.Int64.eq,
            CompCert.Int64.lt, CompCert.Int64.ltu, CompCert.Int64.add,
            CompCert.Int64.sub,
            CompCert.Int64.mul, CompCert.Int64.divu, CompCert.Int64.divs,
            CompCert.Int64.and, CompCert.Int64.or, CompCert.Int64.xor,
            CompCert.Int64.shl, CompCert.Int64.shr, CompCert.Int64.modu] at *))

syntax "simpleproof" : tactic
syntax "autorewritearith" : tactic
syntax "solve_signed_range " ident ident : tactic
syntax "solve_unsigned_range " ident ident : tactic
syntax "solve_unsigned_range_lt " ident ident : tactic
syntax "computedivmul" : tactic
syntax "gen_signed_unsigned_range " term : tactic
syntax "solve_int_unequal" : tactic
syntax "unsigned_range" : tactic
syntax "int_auto_simpl" : tactic
syntax "int_auto_H" : tactic
syntax "int_auto'" : tactic
syntax "int_auto" : tactic
syntax "int" " auto" : tactic

macro_rules
  | `(tactic| simpleproof) =>
      `(tactic|
        first
        | contradiction
        | assumption
        | omega
        | trivial
        | rfl
        | solve_by_elim
        | skip)
  | `(tactic| autorewritearith) =>
      `(tactic| simp only [unsigned_zero, unsigned_one, eq_one_zero, eq_zero_zero,
        negb_true, negb_false, repr_zero, repr_one, and_zero_zero, and_zero_one,
        and_one_zero, and_one_one, or_zero_zero, or_zero_one, or_one_zero,
        or_one_one])
  | `(tactic| solve_signed_range $c:ident $x:ident) =>
      `(tactic|
        have h_range := zdiv_range_le_le Int64.min_signed Int64.max_signed $c
          (Int64.signed $x) (Int.le_of_lt min_signed_lt0) max_signed_gt0 (by omega)
          (Int64.signed_range $x);
        omega)
  | `(tactic| solve_unsigned_range $c:ident $x:ident) =>
      `(tactic|
        have h_range := zdiv_range_le_le 0 Int64.max_unsigned $c
          (Int64.unsigned $x) (by omega) max_unsigned_gt0 (by omega)
          (Int64.unsigned_range_2 $x);
        omega)
  | `(tactic| solve_unsigned_range_lt $c:ident $x:ident) =>
      `(tactic|
        have h_range := zdiv_range_le_lt 0 Int64.max_unsigned $c $x
          (by omega) max_unsigned_gt0 (by omega) (by omega);
        omega)
  | `(tactic| unsigned_range) =>
      `(tactic|
        first
        | (change 0 <= _; try omega)
        | (change _ <= Int64.max_unsigned; rw [max_unsigned_val]; try omega))
  | `(tactic| int_auto') =>
      `(tactic|
        int_auto_H <;>
          first
          | (apply Int64.eqm_samerepr; apply Int64.eqm_refl2; omega)
          | (apply CompCert.Int64.int.ext; change Z.modulo _ _ = Z.modulo _ _; omega)
          | solve_int_unequal)
  | `(tactic| int_auto) =>
      `(tactic|
        intros <;>
        first
        | (apply CompCert.Int64.ltu_add_repr_of_ltu_repr <;>
            first
            | assumption
            | ((try simp only [CompCert.Int64.max_unsigned_val]);
                solve_int_unequal))
        | (int_auto_simpl <;>
            first
            | contradiction
            | assumption
            | omega
            | trivial
            | rfl
            | solve_by_elim
            | (constructor <;> solve_int_unequal)
            | (apply Int64.eqm_samerepr; apply Int64.eqm_refl2; int_auto)
            | (apply repr_eq_word_unsigned; int_auto)
            | (apply word_eq_repr_unsigned; int_auto)
            | (apply CompCert.Int64.int.ext;
                change Z.modulo _ _ = Z.modulo _ _; omega)
            | solve_int_unequal))
  | `(tactic| int auto) => `(tactic| all_goals int_auto)

elab_rules : tactic
  | `(tactic| computedivmul) => withMainContext do
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let goal ← getMainGoal
      let target ← instantiateMVars (← goal.getType)
      let replacement ← match ← reduceFirstOperation target true with
        | some replacement => pure replacement
        | none => match ← reduceFirstOperation target false with
          | some replacement => pure replacement
          | none => throwError
              "computedivmul: goal contains no division or multiplication"
      replaceMainGoal [← goal.change replacement]
  | `(tactic| gen_signed_unsigned_range $e:term) =>
      addIntAutoRangesFromTerm e
  | `(tactic| solve_int_unequal) => runSolveIntUnequal
  | `(tactic| int_auto_simpl) => runIntAutoSimpl
  | `(tactic| int_auto_H) => do
      evalTactic (← `(tactic| int_auto_simpl))
      unless (← getGoals).isEmpty do
        simplifyZdivHypotheses

end AUXLib
