struct int_pair {
    int a;
    int b;
};

/*@ Extern Coq (store_int_pair : Z -> Z -> Z -> Assertion) */
/*@ Extern Coq (store_int_pair_x_only : Z -> Z -> Assertion) */
/*@ Extern Coq (store_int_pair_y_only : Z -> Z -> Assertion) */

/*@ include strategies "swap_simple5.strategies" */
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_tutorial.int_pair_additional_lib */
