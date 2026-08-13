import SimpleC.SL.SeparationLogic

namespace SimpleC.EE.QCP_demos_LLM

open SimpleC.SL.CommonAssertion

inductive tree where
  | empty : tree
  | make_tree : tree -> tree -> tree
deriving DecidableEq

export tree (empty make_tree)

axiom store_tree : Int -> tree -> Assertion
axiom store_tree_shape : Int -> Assertion
axiom store_non_empty_tree : Int -> Assertion
axiom single_tree_node : Int -> Int -> Int -> Int -> Int -> Int -> Assertion

end SimpleC.EE.QCP_demos_LLM
