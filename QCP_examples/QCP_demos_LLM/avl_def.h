struct tree{
    int key;
    int value;
    unsigned char height;
    struct tree *lchild;
    struct tree *rchild;
};

/*@ Extern Coq (tree :: *) */
/*@ Extern Coq (store_tree : Z -> tree -> Assertion)
               (store_tree_shape : Z -> Assertion)
               (store_non_empty_tree : Z -> Assertion)
               (make_tree : tree -> tree -> tree)
               (empty : tree)
               (single_tree_node : Z -> Z -> Z -> Z -> Z -> Z -> Assertion)
*/
/*@ include strategies "avl.strategies" */
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.avl_shape */
/*@ Import Lean import SimpleC.EE.QCP_demos_LLM.avl_shape */
