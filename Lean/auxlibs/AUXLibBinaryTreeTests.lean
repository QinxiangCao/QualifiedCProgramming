import AUXLib.BinaryTree
import Lean.Util.CollectAxioms
import Lean.Meta.Tactic.Simp.Attr

open AUXLib.BinaryTree

open Lean Elab Command Meta

syntax (name := assertNotGlobalSimp) "#assert_not_global_simp " ident : command

elab_rules : command
  | `(#assert_not_global_simp $id:ident) => do
      let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
      let simpTheorems ← liftCoreM Meta.getSimpTheorems
      let origins := #[
        Origin.decl name true false,
        Origin.decl name false false,
        Origin.decl name true true,
        Origin.decl name false true
      ]
      if origins.any simpTheorems.lemmaNames.contains ||
          simpTheorems.toUnfold.contains name then
        throwErrorAt id "declaration '{name}' leaked into the global simp set"

#assert_not_global_simp AUXLib.int_setoidEq_iff
#assert_not_global_simp AUXLib.int_setoidNe_iff

#check Tree.empty
#check Tree.make_tree
#check keys_list_lt
#check Map.merge
#check SearchTree
#check Abs
#check look_up
#check AUXLib.BinaryTree.insert
#check delete
#check swap_delete
#check pushdown_delete
#check IntFacts.insert_SearchTree
#check IntFacts.insert_Abs

namespace SetoidFixture

structure Mod2Key where
  value : Int
deriving DecidableEq

instance : AUXLib.DecidableSetoid Mod2Key where
  eqv x y := x.value % 2 = y.value % 2
  refl _ := rfl
  symm := Eq.symm
  trans := Eq.trans
  decEqv x y := inferInstanceAs (Decidable (x.value % 2 = y.value % 2))

instance : LT Mod2Key where
  lt x y := x.value % 2 < y.value % 2

instance : DecidableLT Mod2Key := fun x y =>
  inferInstanceAs (Decidable (x.value % 2 < y.value % 2))

def zero : Mod2Key := ⟨0⟩
def two : Mod2Key := ⟨2⟩
def customTree : Tree Mod2Key Int := .make_tree .empty zero 7 .empty

example : zero ≠ two := by decide
example : Map.singleton zero 7 two = some 7 := by decide
example : key_set customTree two := by
  exact Or.inr (Or.inl (by change AUXLib.setoidEq two zero; decide))
example : tree_kv customTree two 7 := by
  exact Or.inr (Or.inl ⟨by decide, rfl⟩)
example : look_up two customTree = some 7 := by decide
example : look_up zero (insert two 9 customTree) = some 9 := by decide
example : look_up zero (delete two customTree) = none := by decide
example : look_up zero (swap_delete two customTree) = none := by decide
example : look_up zero (pushdown_delete two customTree) = none := by decide

end SetoidFixture

example {Key Value : Type} [AUXLib.DecidableSetoid Key]
    (tl tr : Tree Key Value) (k : Key) (v : Value)
    (h : tree_kv tl k v \/ tree_kv tr k v) :
    tree_kv (tree_pre_merge tl tr) k v := by
  fail_if_success simpa using h
  exact (tree_pre_merge_tree_kv tl tr k v).mp h

example {Key Value : Type} [AUXLib.DecidableSetoid Key]
    (tl tr : Tree Key Value) (k : Key) (v : Value)
    (h : tree_kv (tree_pre_merge tl tr) k v) :
    tree_kv tl k v \/ tree_kv tr k v :=
  (tree_pre_merge_tree_kv tl tr k v).mpr h

abbrev T := Tree Int Int

def sample : T :=
  .make_tree (.make_tree .empty 1 10 .empty) 2 20
    (.make_tree .empty 3 30 .empty)

example : SearchTree sample := by
  simp [sample, SearchTree, keys_key_lt, key_keys_lt, key_set, set_union,
    Sets_singleton_setoid, empty_set, AUXLib.int_setoidEq_iff]

example : look_up 1 sample = some 10 := by decide
example : look_up 4 sample = none := by decide
example : look_up 2 (insert 2 99 sample) = some 99 := by decide
example : look_up 4 (insert 4 40 sample) = some 40 := by decide
example : look_up 2 (delete 2 sample) = none := by decide
example : look_up 2 (swap_delete 2 sample) = none := by decide

example : SearchTree (insert 4 40 sample) := by
  apply IntFacts.insert_SearchTree
  simp [sample, SearchTree, keys_key_lt, key_keys_lt, key_set, set_union,
    Sets_singleton_setoid, empty_set, AUXLib.int_setoidEq_iff]

def sampleMap : Mapping Int Int
  | 1 => some 10
  | 2 => some 20
  | 3 => some 30
  | _ => none

example : Abs sample sampleMap := by
  intro k v
  by_cases h1 : k = 1
  · subst k; simp [sample, sampleMap, tree_kv, eq_comm, AUXLib.int_setoidEq_iff]
  by_cases h2 : k = 2
  · subst k; simp [sample, sampleMap, tree_kv, eq_comm, AUXLib.int_setoidEq_iff]
  by_cases h3 : k = 3
  · subst k; simp [sample, sampleMap, tree_kv, eq_comm, AUXLib.int_setoidEq_iff]
  simp [sample, sampleMap, tree_kv, h1, h2, h3, AUXLib.int_setoidEq_iff]

#print axioms AUXLib.BinaryTree.IntFacts.insert_SearchTree
#print axioms AUXLib.BinaryTree.IntFacts.insert_Abs
