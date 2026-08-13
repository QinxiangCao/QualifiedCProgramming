struct tree {
  int key;
  int value;
  struct tree *father;
  struct tree *left;
  struct tree *right;
};

/*@ Extern Coq (tree :: *) */
/*@ Extern Coq (partial_tree :: *) */
/*@ Extern Coq (mapping :: *) */
/*@ Extern Coq (Bst::store_map : Z -> mapping -> Assertion)
               (store_tree : Z -> Z -> tree -> Assertion)
               (store_ptb: Z -> Z -> Z -> Z -> partial_tree -> Assertion)
               (empty_partial_tree: partial_tree)
               (combine_tree: partial_tree -> tree -> tree)
               (make_tree: tree -> Z -> Z -> tree -> tree)
               (tree_insert: Z -> Z -> tree -> tree)
               (map_insert: Z -> Z -> mapping -> mapping)
               (tree_delete: Z -> tree -> tree)
               (map_delete: Z -> mapping -> mapping)
               (store_pt: Z -> Z -> Z -> Z -> partial_tree -> Assertion)
               (min_key: Z -> tree -> Z)
               (min_value: Z -> tree -> Z)
               (delete_min: tree -> tree) */

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.bst_fp_lib */
/*@ Import Lean import SimpleC.EE.QCP_demos_LLM.bst_fp_lib */

/*@ include strategies "bst_fp.strategies"*/
