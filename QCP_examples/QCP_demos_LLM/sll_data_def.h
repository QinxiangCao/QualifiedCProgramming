struct list {
   int data;
   struct list *next;
};

/*@ Extern Coq (sll : Z -> list Z -> Assertion)
               (sllseg: Z -> Z -> list Z -> Assertion)
 */

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.sll_lib */

/*@ include strategies "sll_data.strategies" */
