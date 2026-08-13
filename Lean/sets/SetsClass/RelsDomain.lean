import Std.Tactic
import Lean.Elab.Tactic
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Revert
import Lean.Util.CollectFVars
import Lean.Util.ReplaceExpr
import SetsClass.SetsDomain

namespace Rels

class ACCUM (I1 I2 I : Type) where
  app : I1 -> I2 -> I

class ACCUM_NIL (I : Type) where
  nil : I

class ACCUM_EQ (I : Type) where
  i_equiv : I -> I -> Prop

class PRE_RELS (A R S T : Type) where
  concat_aux : R -> S -> A -> T

class PRE_RELS_ID (A R : Type) where
  id_aux : A -> R

class RELS (R S T : Type) where
  concat : R -> S -> T

class RELS_ID (R : Type) where
  id : R

class RELS_TEST (S R : Type) where
  test : S -> R

abbrev app {I1 I2 I : Type} [a : ACCUM I1 I2 I] : I1 -> I2 -> I := a.app
abbrev nil {I : Type} [n : ACCUM_NIL I] : I := n.nil
abbrev i_equiv {I : Type} [e : ACCUM_EQ I] : I -> I -> Prop := e.i_equiv
abbrev concat_aux {A R S T : Type} [r : PRE_RELS A R S T] : R -> S -> A -> T :=
  r.concat_aux
abbrev id_aux {A R : Type} [r : PRE_RELS_ID A R] : A -> R := r.id_aux
abbrev concat {R S T : Type} [r : RELS R S T] : R -> S -> T := r.concat
abbrev id {R : Type} [r : RELS_ID R] : R := r.id
abbrev test {S R : Type} [r : RELS_TEST S R] : S -> R := r.test

end Rels

instance Prop_PRE_RELS (A S : Type) [Sets.SETS S] :
    Rels.PRE_RELS A (A -> Prop) S S where
  concat_aux X Y a := Sets.intersect (Sets.test1 X a) Y

instance Prop_PRE_RELS_ID (A : Type) : Rels.PRE_RELS_ID A (A -> Prop) where
  id_aux a b := a = b

instance lift_PRE_RELS (I1 I2 I A R S T : Type) [Rels.PRE_RELS A R S T]
    [Rels.ACCUM I1 I2 I] [Sets.SETS T] :
    Rels.PRE_RELS A (I1 -> R) (I2 -> S) (I -> T) where
  concat_aux X Y a i :=
    Sets.indexed_union (fun i2 =>
      Sets.indexed_union (fun i1 =>
        Sets.intersect (Sets.prop_inj (Rels.app i1 i2 = i))
          (Rels.concat_aux (X i1) (Y i2) a)))

instance lift_PRE_RELS_ID (I A T : Type) [Rels.PRE_RELS_ID A T]
    [Rels.ACCUM_NIL I] [Sets.SETS T] :
    Rels.PRE_RELS_ID A (I -> T) where
  id_aux a i :=
    Sets.intersect (Sets.prop_inj (i = Rels.nil)) (Rels.id_aux a)

instance Derived_RELS (B A R S T : Type) [Rels.PRE_RELS A R S T]
    [Sets.SETS T] : Rels.RELS (B -> R) (A -> S) (B -> T) where
  concat X Y a := Sets.indexed_union (fun b => Rels.concat_aux (X a) (Y b) b)

instance Derived_RELS_ID (A T : Type) [Rels.PRE_RELS_ID A T] [Sets.SETS T] :
    Rels.RELS_ID (A -> T) where
  id := Rels.id_aux

instance Derived_RELS_TEST (A T : Type) [Rels.PRE_RELS_ID A T] [Sets.SETS T] :
    Rels.RELS_TEST (A -> Prop) (A -> T) where
  test X := Sets.filter1 X Rels.id

class ACCUM_Assoc (I1 I2 I3 I12 I23 I123 : Type)
    [acc12 : Rels.ACCUM I1 I2 I12] [acc23 : Rels.ACCUM I2 I3 I23]
    [acc123l : Rels.ACCUM I12 I3 I123]
    [acc123r : Rels.ACCUM I1 I23 I123] : Prop where
  Rels_app_assoc : forall (i1 : I1) (i2 : I2) (i3 : I3),
    @Rels.app I12 I3 I123 acc123l (@Rels.app I1 I2 I12 acc12 i1 i2) i3 =
      @Rels.app I1 I23 I123 acc123r i1 (@Rels.app I2 I3 I23 acc23 i2 i3)

class ACCUM_LeftId (I1 I2 : Type) [acc : Rels.ACCUM I1 I2 I2]
    [accNil : Rels.ACCUM_NIL I1] : Prop where
  Rels_app_nil_l_setoid : forall i : I2,
    @Rels.app I1 I2 I2 acc (@Rels.nil I1 accNil) i = i

class ACCUM_RightId (I1 I2 : Type) [acc : Rels.ACCUM I1 I2 I1]
    [accNil : Rels.ACCUM_NIL I2] : Prop where
  Rels_app_nil_r_setoid : forall i : I1,
    @Rels.app I1 I2 I1 acc i (@Rels.nil I2 accNil) = i

namespace ListConn

instance list_ACC (A : Type) : Rels.ACCUM (List A) (List A) (List A) where
  app := List.append

instance list_ACC_Nil (A : Type) : Rels.ACCUM_NIL (List A) where
  nil := []

instance list_ACC_LeftId (A : Type) :
    _root_.ACCUM_LeftId (List A) (List A) where
  Rels_app_nil_l_setoid := by intro i; rfl

instance list_ACC_RightId (A : Type) :
    _root_.ACCUM_RightId (List A) (List A) where
  Rels_app_nil_r_setoid := List.append_nil

instance list_ACC_Assoc (A : Type) :
    _root_.ACCUM_Assoc (List A) (List A) (List A) (List A) (List A) (List A) where
  Rels_app_assoc := List.append_assoc

end ListConn

def nsteps {X : Type} [Rels.RELS X X X] [Rels.RELS_ID X]
    (x : X) : Nat -> X
  | 0 => Rels.id
  | n + 1 => Rels.concat x (nsteps x n)

def clos_refl_trans {X : Type} [Rels.RELS X X X] [Rels.RELS_ID X]
    [Sets.SETS X] (x : X) : X :=
  Sets.indexed_union (nsteps x)

def nsteps' {X : Type} [Rels.RELS X X X] [Rels.RELS_ID X]
    (x : X) : Nat -> X
  | 0 => Rels.id
  | n + 1 => Rels.concat (nsteps' x n) x

theorem nsteps_rt {X : Type} [Rels.RELS X X X] [Rels.RELS_ID X]
    [Sets.SETS X] [SETS_Properties X] (x : X) (n : Nat) :
    Sets.included (nsteps x n) (clos_refl_trans x) :=
  Sets_included_indexed_union (I := Nat) n (nsteps x)

instance rt2_refl_ins (A : Type) (R : A -> A -> Prop) :
    AUXLib.Reflexive (clos_refl_trans R) where
  refl x := ⟨0, rfl⟩

theorem nsteps_rel_add (A : Type) (R : A -> A -> Prop)
    (n m : Nat) {x y z : A} :
    nsteps R n x y -> nsteps R m y z -> nsteps R (n + m) x z := by
  intro hn hm
  induction n generalizing x with
  | zero =>
      simp only [nsteps] at hn
      subst y
      simpa using hm
  | succ n ih =>
      rcases hn with ⟨q, hxq, hqy⟩
      simp only [Nat.succ_add, nsteps]
      exact ⟨q, hxq, ih hqy⟩

instance rt2_trans_ins (A : Type) (R : A -> A -> Prop) :
    AUXLib.Transitive (clos_refl_trans R) where
  trans x y z hxy hyz := by
    rcases hxy with ⟨n, hn⟩
    rcases hyz with ⟨m, hm⟩
    exact ⟨n + m, nsteps_rel_add A R n m hn hm⟩

theorem clos_refl_trans_cases (A : Type) (R : A -> A -> Prop) {x z : A}
    (h : clos_refl_trans R x z) :
    x = z \/ exists y, R x y /\ clos_refl_trans R y z := by
  rcases h with ⟨n, hn⟩
  cases n with
  | zero => exact Or.inl hn
  | succ n =>
      rcases hn with ⟨y, hxy, hyz⟩
      exact Or.inr ⟨y, hxy, ⟨n, hyz⟩⟩

def clos_refl_trans_cons {A : Type} {R : A -> A -> Prop}
    {x y z : A} (hxy : R x y) (hyz : clos_refl_trans R y z) :
    clos_refl_trans R x z :=
  match hyz with
  | ⟨n, hn⟩ => ⟨n + 1, y, hxy, hn⟩

@[elab_as_elim]
theorem clos_refl_trans_induction_1n {A : Type} {R : A -> A -> Prop}
    {motive : forall x z, clos_refl_trans R x z -> Prop}
    {x z : A} (h : clos_refl_trans R x z)
    (hrefl : forall x, motive x x ⟨0, rfl⟩)
    (hstep : forall x y z (hxy : R x y) (hyz : clos_refl_trans R y z),
      motive y z hyz -> motive x z (clos_refl_trans_cons hxy hyz)) :
    motive x z h := by
  rcases h with ⟨n, hn⟩
  induction n generalizing x with
  | zero =>
      simp only [nsteps] at hn
      subst z
      exact hrefl x
  | succ n ih =>
      simp only [nsteps] at hn
      rcases hn with ⟨y, hxy, hyz⟩
      exact hstep x y z hxy ⟨n, hyz⟩ (ih hyz)

private theorem nsteps_succ_last (A : Type) (R : A -> A -> Prop)
    (n : Nat) {x z : A} (h : nsteps R (n + 1) x z) :
    exists y, nsteps R n x y /\ R y z := by
  induction n generalizing x with
  | zero =>
      simp only [nsteps] at h
      rcases h with ⟨y, hxy, rfl⟩
      exact ⟨x, rfl, hxy⟩
  | succ n ih =>
      simp only [nsteps] at h
      rcases h with ⟨q, hxq, hqz⟩
      rcases ih hqz with ⟨y, hqy, hyz⟩
      exact ⟨y, ⟨q, hxq, hqy⟩, hyz⟩

def clos_refl_trans_snoc {A : Type} {R : A -> A -> Prop}
    {x y z : A} (hxy : clos_refl_trans R x y) (hyz : R y z) :
    clos_refl_trans R x z :=
  match hxy with
  | ⟨n, hn⟩ =>
      ⟨n + 1, nsteps_rel_add A R n 1 hn ⟨z, hyz, rfl⟩⟩

@[elab_as_elim]
theorem clos_refl_trans_induction_n1 {A : Type} {R : A -> A -> Prop}
    {motive : forall x z, clos_refl_trans R x z -> Prop}
    {x z : A} (h : clos_refl_trans R x z)
    (hrefl : forall x, motive x x ⟨0, rfl⟩)
    (hstep : forall x y z (hxy : clos_refl_trans R x y) (hyz : R y z),
      motive x y hxy -> motive x z (clos_refl_trans_snoc hxy hyz)) :
    motive x z h := by
  rcases h with ⟨n, hn⟩
  induction n generalizing z with
  | zero =>
      simp only [nsteps] at hn
      subst z
      exact hrefl x
  | succ n ih =>
      rcases nsteps_succ_last A R n hn with ⟨y, hxy, hyz⟩
      have result := hstep x y z ⟨n, hxy⟩ hyz (ih hxy)
      have heq : clos_refl_trans_snoc ⟨n, hxy⟩ hyz = ⟨n + 1, hn⟩ :=
        Subsingleton.elim _ _
      exact heq ▸ result

private structure PreparedClosureInduction where
  binders : Array Lean.FVarId
  proof : Lean.FVarId

private def prepareClosureInduction (h : Lean.Syntax) :
    Lean.Elab.Tactic.TacticM PreparedClosureInduction := do
  let goal <- Lean.Elab.Tactic.getMainGoal
  let hId <- Lean.Elab.Tactic.getFVarId h
  goal.withContext do
    let hType <- Lean.instantiateMVars (← Lean.Meta.inferType (Lean.mkFVar hId))
    let args := hType.getAppArgs
    unless hType.getAppFn.isConstOf ``clos_refl_trans && args.size >= 2 do
      Lean.Elab.throwAbortTactic
    let endpointState := Lean.collectFVars (Lean.collectFVars {} args[args.size - 2]!)
      args[args.size - 1]!
    let (reverted, revertedGoal) <- goal.revert endpointState.fvarIds true
    let mut introCount := 0
    for fvarId in reverted do
      introCount := introCount + 1
      if fvarId == hId then
        break
    if introCount == 0 || introCount > reverted.size then
      Lean.Elab.throwAbortTactic
    let freshHName <- Lean.mkFreshUserName `_closure_h
    let mut names : List Lean.Name := []
    for fvarId in reverted.take introCount do
      let name <- if fvarId == hId then pure freshHName else pure (← fvarId.getDecl).userName
      names := names ++ [name]
    let (introduced, preparedGoal) <- revertedGoal.introN introCount names
    Lean.Elab.Tactic.setGoals [preparedGoal]
    return ⟨introduced, introduced[introCount - 1]!⟩

private def applyClosureInduction (prepared : PreparedClosureInduction)
    (eliminatorName : Lean.Name) :
    Lean.Elab.Tactic.TacticM Unit := do
  let goal <- Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    let hExpr := Lean.mkFVar prepared.proof
    let hType <- Lean.instantiateMVars (← Lean.Meta.inferType hExpr)
    let args := hType.getAppArgs
    unless hType.getAppFn.isConstOf ``clos_refl_trans && args.size >= 3 do
      Lean.Elab.throwAbortTactic
    let relation := args[args.size - 3]!
    let x := args[args.size - 2]!
    let z := args[args.size - 1]!
    let stateType <- Lean.Meta.inferType x
    let target <- goal.getType
    let motive <- Lean.Meta.withLocalDeclD `x stateType fun a =>
      Lean.Meta.withLocalDeclD `z stateType fun b => do
        let closure <- Lean.Meta.mkAppM ``clos_refl_trans #[relation, a, b]
        Lean.Meta.withLocalDeclD `h closure fun hp =>
          Lean.Meta.mkLambdaFVars #[a, b, hp]
            (target.replace fun e =>
              if e == x then some a
              else if e == z then some b
              else if e == hExpr then some hp
              else none)
    let eliminatorConst <- Lean.Meta.mkConstWithFreshMVarLevels eliminatorName
    let eliminator := Lean.mkAppN eliminatorConst #[stateType, relation, motive, x, z, hExpr]
    let goals <- goal.apply eliminator
    Lean.Elab.Tactic.setGoals (← goals.mapM fun next => next.tryClearMany prepared.binders)

syntax "induction_1n" ident : tactic
syntax "induction_n1" ident : tactic

elab_rules : tactic
  | `(tactic| induction_1n $h:ident) => do
      let prepared <- prepareClosureInduction h
      applyClosureInduction prepared ``clos_refl_trans_induction_1n
      Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals intros))
  | `(tactic| induction_n1 $h:ident) => do
      let prepared <- prepareClosureInduction h
      applyClosureInduction prepared ``clos_refl_trans_induction_n1
      Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals intros))
