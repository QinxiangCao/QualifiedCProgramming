struct tree {
  int key;
  int value;
  struct tree *left;
  struct tree *right;
};

/*@ Extern Coq (tree :: *) */
/*@ Extern Coq (partial_tree :: *) */
/*@ Extern Coq (mapping :: *) */
/*@ Extern Coq Record result {
  pt : partial_tree;
  k : Z;
  v : Z;
  l_tree : tree;
} */
/*@ Extern Coq (Bst::store_map : Z -> mapping -> Assertion)
               (store_tree : Z -> tree -> Assertion)
               (store_ptb: Z -> Z -> partial_tree -> Assertion)
               (store_pt: Z -> Z -> partial_tree -> Assertion)
               (empty: tree)
               (empty_partial_tree: partial_tree)
               (combine_tree: partial_tree -> tree -> tree)
               (make_tree: tree -> Z -> Z -> tree -> tree)
               (tree_pre_merge : tree -> tree -> tree)
               (tree_delete: Z -> tree -> tree)
               (find_pre: tree -> Z -> Z -> tree -> result)
               (tree_delete': Z -> tree -> tree)
               (map_delete: Z -> mapping -> mapping) 
               (tree_insert: Z -> Z -> tree -> tree)
               (map_insert: Z -> Z -> mapping -> mapping)
               */ 

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.bst_lib */
/*@ Import Coq Import get_right_most*/
/*@ Import Lean import SimpleC.EE.QCP_demos_LLM.bst_lib */
/*@ Import Lean open SimpleC.EE.QCP_demos_LLM.Bst */

/*@ include strategies "bst.strategies"*/
