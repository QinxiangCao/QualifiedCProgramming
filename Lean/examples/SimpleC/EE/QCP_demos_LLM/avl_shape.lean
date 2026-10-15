import SimpleC.SL.SeparationLogic

namespace SimpleC.EE.QCP_demos_LLM

open SimpleC.SL.CommonAssertion SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CNotation SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC
local instance avl_shapeSacContext : SacContext := ⟨naive_C_Rules⟩

inductive tree where
  | empty : tree
  | make_tree : tree -> tree -> tree
deriving DecidableEq

export tree (empty make_tree)

noncomputable def store_tree (p : Int) : tree → Assertion
  | .empty => “ p = NULL ” && emp
  | .make_tree l r => EX pl : Int, EX pr : Int, EX k : Int, EX v : Int, EX h : Int,
      “ p ≠ NULL ” &&
      (&(p # "tree" ->ₛ "key") # INT |-> k) **
      (&(p # "tree" ->ₛ "value") # INT |-> v) **
      (&(p # "tree" ->ₛ "height") # UCHAR |-> h) **
      (&(p # "tree" ->ₛ "lchild") # PTR |-> pl) **
      (&(p # "tree" ->ₛ "rchild") # PTR |-> pr) ** store_tree pl l ** store_tree pr r

noncomputable def store_tree_shape (p : Int) : Assertion := EX tr : tree, store_tree p tr
noncomputable def store_non_empty_tree (p : Int) : Assertion := “ p ≠ NULL ” && store_tree_shape p
noncomputable def single_tree_node (p k v h l r : Int) : Assertion :=
  (&(p # "tree" ->ₛ "key") # INT |-> k) **
  (&(p # "tree" ->ₛ "value") # INT |-> v) **
  (&(p # "tree" ->ₛ "height") # UCHAR |-> h) **
  (&(p # "tree" ->ₛ "lchild") # PTR |-> l) **
  (&(p # "tree" ->ₛ "rchild") # PTR |-> r)

end SimpleC.EE.QCP_demos_LLM
