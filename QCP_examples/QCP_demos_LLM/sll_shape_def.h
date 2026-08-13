struct list {
   int data;
   struct list *next;
};

/*@ Extern Coq (listrep : Z -> Assertion)
               (lseg: Z -> Z -> Assertion)
               (listboxseg: Z -> Z -> Assertion)
               (sll_tag : Z -> Prop)
 */

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.sll_shape_lib */
/*@ Import Lean import SimpleC.EE.QCP_demos_LLM.sll_shape_lib */

/*@ include strategies "sll_shape.strategies" */
