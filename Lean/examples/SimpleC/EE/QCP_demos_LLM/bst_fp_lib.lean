import SimpleC.EE.QCP_demos_LLM.bst_base_lib

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace SimpleC.EE.QCP_demos_LLM.bst_fp_lib

open AUXLib.BinaryTree
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance bst_fp_libSacContext : SacContext := ⟨naive_C_Rules⟩

abbrev key := Int
abbrev value := Int
abbrev tree := Tree Int Int
abbrev mapping := Mapping Int Int

def empty : tree := .empty
def make_tree (l : tree) (k v : Int) (r : tree) : tree := .make_tree l k v r

namespace Key

abbrev Decision := SimpleC.EE.QCP_demos_LLM.bst_base_lib.Key.Decision
def dec := SimpleC.EE.QCP_demos_LLM.bst_base_lib.Key.dec

end Key

abbrev SearchTree : tree -> Prop := AUXLib.BinaryTree.SearchTree
abbrev Abs : tree -> mapping -> Prop := AUXLib.BinaryTree.Abs

namespace Map
abbrev insert := AUXLib.BinaryTree.Map.insert (Key := Int) (Value := Int)
abbrev delete := AUXLib.BinaryTree.Map.delete (Key := Int) (Value := Int)
end Map

inductive half_tree : Type where
  | LH (k v : Int) (right : tree)
  | RH (k v : Int) (left : tree)
  deriving Repr

export half_tree (LH RH)
abbrev partial_tree := List half_tree

def combine_tree : partial_tree -> tree -> tree
  | [], tr => tr
  | LH k v r :: pt, tr => combine_tree pt (.make_tree tr k v r)
  | RH k v l :: pt, tr => combine_tree pt (.make_tree l k v tr)

def empty_partial_tree : partial_tree := []

def tree_insert (x v : Int) : tree -> tree := AUXLib.BinaryTree.insert x v

def min_key (default : Int) (tr : tree) : Int :=
  (min_node (default, 0) tr).1

def min_value (default : Int) (tr : tree) : Int :=
  (min_node (0, default) tr).2

def delete_min : tree -> tree := AUXLib.BinaryTree.delete_min

def tree_delete (x : Int) : tree -> tree := AUXLib.BinaryTree.swap_delete x

theorem tree_insert_same_def (x v : Int) :
    tree_insert x v = AUXLib.BinaryTree.insert x v := rfl

theorem delete_min_same_def (tr : tree) :
    delete_min tr = AUXLib.BinaryTree.delete_min tr := rfl

theorem tree_delete_same_def (x : Int) (tr : tree) :
    tree_delete x tr = AUXLib.BinaryTree.swap_delete x tr := rfl

theorem min_key_as_min_node (keyDefault valueDefault : Int)
    (l : tree) (k v : Int) (r : tree) :
    min_key keyDefault (make_tree l k v r) =
      (min_node (keyDefault, valueDefault) (make_tree l k v r)).1 := by
  unfold min_key make_tree
  exact congrArg Prod.fst
    (min_node_same_def (keyDefault, 0) (keyDefault, valueDefault) l k v r)

theorem min_value_as_min_node (keyDefault valueDefault : Int)
    (l : tree) (k v : Int) (r : tree) :
    min_value valueDefault (make_tree l k v r) =
      (min_node (keyDefault, valueDefault) (make_tree l k v r)).2 := by
  unfold min_value make_tree
  exact congrArg Prod.snd
    (min_node_same_def (0, valueDefault) (keyDefault, valueDefault) l k v r)

abbrev map_insert := Map.insert
abbrev map_delete := Map.delete

noncomputable abbrev tree_key_addr (p : Int) : addr :=
  addr_notation (LE_arrow_field (RE_const p (FET_alias "tree")) "key")
noncomputable abbrev tree_value_addr (p : Int) : addr :=
  addr_notation (LE_arrow_field (RE_const p (FET_alias "tree")) "value")
noncomputable abbrev tree_left_addr (p : Int) : addr :=
  addr_notation (LE_arrow_field (RE_const p (FET_alias "tree")) "left")
noncomputable abbrev tree_right_addr (p : Int) : addr :=
  addr_notation (LE_arrow_field (RE_const p (FET_alias "tree")) "right")
noncomputable abbrev tree_father_addr (p : Int) : addr :=
  addr_notation (LE_arrow_field (RE_const p (FET_alias "tree")) "father")

def store_tree (p p_fa : addr) : tree -> Assertion
  | .empty => “ p = NULL ” && emp
  | .make_tree l k v r =>
      “ p ≠ NULL ” && “ INT_MIN <= k /\ k <= INT_MAX ” &&
      (EX pl : addr, EX pr : addr,
        store_int naive_C_Rules (tree_key_addr p) k **
        store_int naive_C_Rules (tree_value_addr p) v **
        store_ptr naive_C_Rules (tree_left_addr p) pl **
        store_ptr naive_C_Rules (tree_right_addr p) pr **
        store_ptr naive_C_Rules (tree_father_addr p) p_fa **
        store_tree pl p l ** store_tree pr p r)

def store_ptb (p2 p2_root p_fa p_root_fa : addr) : partial_tree -> Assertion
  | [] => “ p2 = p2_root ” && “ p_fa = p_root_fa ” && emp
  | LH k v tr :: pt =>
      EX p2_fa : addr, EX p_bro : addr, EX p_gfa : addr,
        “ p_fa ≠ NULL ” && “ INT_MIN <= k /\ k <= INT_MAX ” &&
        “ tree_left_addr p_fa = p2 ” &&
        store_ptr naive_C_Rules p2_fa p_fa **
        store_int naive_C_Rules (tree_key_addr p_fa) k **
        store_int naive_C_Rules (tree_value_addr p_fa) v **
        store_ptr naive_C_Rules (tree_right_addr p_fa) p_bro **
        store_ptr naive_C_Rules (tree_father_addr p_fa) p_gfa **
        store_tree p_bro p_fa tr **
        store_ptb p2_fa p2_root p_gfa p_root_fa pt
  | RH k v tr :: pt =>
      EX p2_fa : addr, EX p_bro : addr, EX p_gfa : addr,
        “ p_fa ≠ NULL ” && “ INT_MIN <= k /\ k <= INT_MAX ” &&
        “ tree_right_addr p_fa = p2 ” &&
        store_ptr naive_C_Rules p2_fa p_fa **
        store_int naive_C_Rules (tree_key_addr p_fa) k **
        store_int naive_C_Rules (tree_value_addr p_fa) v **
        store_ptr naive_C_Rules (tree_left_addr p_fa) p_bro **
        store_ptr naive_C_Rules (tree_father_addr p_fa) p_gfa **
        store_tree p_bro p_fa tr **
        store_ptb p2_fa p2_root p_gfa p_root_fa pt

attribute [irreducible] store_tree store_ptb

namespace Bst
def store_map (p : addr) (m : mapping) : Assertion :=
  EX tr : tree, “ SearchTree tr ” && “ Abs tr m ” && store_tree p 0 tr
end Bst

theorem insert_SearchTree (tr : tree) (k v : Int) (h : SearchTree tr) :
    SearchTree (tree_insert k v tr) := IntFacts.insert_SearchTree tr k v h

theorem insert_Abs (tr : tree) (m : mapping) (k v : Int)
    (hst : SearchTree tr) (habs : Abs tr m) :
    Abs (tree_insert k v tr) (map_insert k v m) :=
  IntFacts.insert_Abs tr m k v hst habs

theorem delete_SearchTree (tr : tree) (k : Int) (h : SearchTree tr) :
    SearchTree (tree_delete k tr) := IntFacts.swap_delete_SearchTree tr k h

theorem delete_Abs (tr : tree) (m : mapping) (k : Int)
    (hst : SearchTree tr) (habs : Abs tr m) :
    Abs (tree_delete k tr) (map_delete k m) :=
  IntFacts.swap_delete_Abs tr m k hst habs

theorem store_ptb_LH (p2_fa p_fa p_bro p_gfa k v : Int) (tr : tree)
    (hp : p_fa ≠ NULL) (hk : INT_MIN <= k /\ k <= INT_MAX) :
    store_ptr naive_C_Rules p2_fa p_fa **
      store_int naive_C_Rules (tree_key_addr p_fa) k **
      store_int naive_C_Rules (tree_value_addr p_fa) v **
      store_ptr naive_C_Rules (tree_right_addr p_fa) p_bro **
      store_ptr naive_C_Rules (tree_father_addr p_fa) p_gfa **
      store_tree p_bro p_fa tr |--
    store_ptb (tree_left_addr p_fa) p2_fa p_fa p_gfa [LH k v tr] := by
  simp only [store_ptb]
  Exists p2_fa p_bro p_gfa
  entailer!

theorem store_ptb_RH (p2_fa p_fa p_bro p_gfa k v : Int) (tr : tree)
    (hp : p_fa ≠ NULL) (hk : INT_MIN <= k /\ k <= INT_MAX) :
    store_ptr naive_C_Rules p2_fa p_fa **
      store_int naive_C_Rules (tree_key_addr p_fa) k **
      store_int naive_C_Rules (tree_value_addr p_fa) v **
      store_ptr naive_C_Rules (tree_left_addr p_fa) p_bro **
      store_ptr naive_C_Rules (tree_father_addr p_fa) p_gfa **
      store_tree p_bro p_fa tr |--
    store_ptb (tree_right_addr p_fa) p2_fa p_fa p_gfa [RH k v tr] := by
  simp only [store_ptb]
  Exists p2_fa p_bro p_gfa
  entailer!

theorem store_ptb_app (p2 p2_mid p2_root p_fa p_mid_fa p_root_fa : Int)
    (pt1 pt2 : partial_tree) :
    store_ptb p2 p2_mid p_fa p_mid_fa pt1 **
      store_ptb p2_mid p2_root p_mid_fa p_root_fa pt2 |--
    store_ptb p2 p2_root p_fa p_root_fa (pt1 ++ pt2) := by
  induction pt1 generalizing p2 p_fa with
  | nil =>
      simp only [store_ptb, List.nil_append]
      Intros
      subst p2
      subst p_fa
      entailer!
  | cons h pt ih =>
      cases h with
      | LH k v tr =>
          simp only [store_ptb, List.cons_append]
          Intros p2_fa p_bro p_gfa
          Exists p2_fa p_bro p_gfa
          entailer!
      | RH k v tr =>
          simp only [store_ptb, List.cons_append]
          Intros p2_fa p_bro p_gfa
          Exists p2_fa p_bro p_gfa
          entailer!

theorem store_tree_zero (p p_fa : Int) (tr : tree) (hp : p = 0) :
    store_tree p p_fa tr |-- “ tr = empty ” && emp := by
  subst p
  cases tr with
  | empty => simp only [store_tree, empty]; entailer!
  | make_tree l k v r => simp only [store_tree]; entailer!

theorem store_tree_not_zero (p p_fa : Int) (tr : tree) (hp : p ≠ 0) :
    store_tree p p_fa tr |--
      EX l : tree, EX k : Int, EX v : Int, EX r : tree,
      EX pl : Int, EX pr : Int,
        “ tr = make_tree l k v r ” &&
        “ INT_MIN <= k /\ k <= INT_MAX ” && “ p ≠ NULL ” &&
        “ INT_MIN <= k /\ k <= INT_MAX ” &&
        store_int naive_C_Rules (tree_key_addr p) k **
        store_int naive_C_Rules (tree_value_addr p) v **
        store_ptr naive_C_Rules (tree_left_addr p) pl **
        store_ptr naive_C_Rules (tree_right_addr p) pr **
        store_ptr naive_C_Rules (tree_father_addr p) p_fa **
        store_tree pl p l ** store_tree pr p r := by
  cases tr with
  | empty => simp only [store_tree]; entailer!
  | make_tree l k v r =>
      simp only [store_tree]
      Intros pl pr
      Exists l k v r pl pr
      entailer!

theorem store_tree_size_1 (p p_fa k v : Int) (hp : p ≠ 0)
    (hk : INT_MIN <= k /\ k <= INT_MAX) :
    store_int naive_C_Rules (tree_key_addr p) k **
      store_int naive_C_Rules (tree_value_addr p) v **
      store_ptr naive_C_Rules (tree_left_addr p) 0 **
      store_ptr naive_C_Rules (tree_right_addr p) 0 **
      store_ptr naive_C_Rules (tree_father_addr p) p_fa |--
    store_tree p p_fa (make_tree empty k v empty) := by
  simp only [store_tree, make_tree, empty]
  Exists (0 : Int) (0 : Int)
  entailer!

theorem store_tree_make_tree (p k v pl pr p_fa : Int) (l r : tree)
    (hp : p ≠ 0) (hk : INT_MIN <= k /\ k <= INT_MAX) :
    store_int naive_C_Rules (tree_key_addr p) k **
      store_int naive_C_Rules (tree_value_addr p) v **
      store_ptr naive_C_Rules (tree_left_addr p) pl **
      store_ptr naive_C_Rules (tree_right_addr p) pr **
      store_ptr naive_C_Rules (tree_father_addr p) p_fa **
      store_tree pl p l ** store_tree pr p r |--
    store_tree p p_fa (make_tree l k v r) := by
  simp only [store_tree, make_tree]
  Exists pl pr
  entailer!

theorem store_ptb_store_tree (p2_root p2 p p_fa p_root_fa : Int)
    (pt : partial_tree) (tr : tree) :
    store_ptb p2 p2_root p_fa p_root_fa pt **
      store_ptr naive_C_Rules p2 p ** store_tree p p_fa tr |--
    EX p_root : Int,
      store_ptr naive_C_Rules p2_root p_root **
        store_tree p_root p_root_fa (combine_tree pt tr) := by
  induction pt generalizing p2 p p_fa tr with
  | nil =>
      simp only [store_ptb, combine_tree]
      Intros
      subst p2
      subst p_fa
      Exists p
      entailer!
  | cons h pt ih =>
      cases h with
      | LH k v sibling =>
          simp only [store_ptb, combine_tree]
          Intros p2_fa p_bro p_gfa
          subst p2
          sep_apply (store_tree_make_tree p_fa k v p p_bro p_gfa tr sibling) <;>
            try assumption
          sep_apply (ih p2_fa p_fa p_gfa (make_tree tr k v sibling))
          Intros p_root
          Exists p_root
          entailer!
      | RH k v sibling =>
          simp only [store_ptb, combine_tree]
          Intros p2_fa p_bro p_gfa
          subst p2
          sep_apply (store_tree_make_tree p_fa k v p_bro p p_gfa sibling tr) <;>
            try assumption
          sep_apply (ih p2_fa p_fa p_gfa (make_tree sibling k v tr))
          Intros p_root
          Exists p_root
          entailer!

end SimpleC.EE.QCP_demos_LLM.bst_fp_lib

namespace SimpleC.EE.QCP_demos_LLM

namespace Bst
export SimpleC.EE.QCP_demos_LLM.bst_fp_lib.Bst (store_map)
end Bst

export SimpleC.EE.QCP_demos_LLM.bst_fp_lib
  (tree empty make_tree tree_insert tree_delete min_key min_value delete_min map_insert map_delete
   SearchTree Abs mapping partial_tree combine_tree empty_partial_tree store_tree store_ptb)

end SimpleC.EE.QCP_demos_LLM
