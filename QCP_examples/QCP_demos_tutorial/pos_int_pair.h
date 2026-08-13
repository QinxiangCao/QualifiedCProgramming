struct int_pair {
    int a;
    int b;
};

/*@ Extern Coq (store_pos_int_pair : Z -> Z -> Z -> Assertion) */
/*@ Extern Coq (store_pos_int_pair_x_only : Z -> Z -> Z -> Assertion) */
/*@ Extern Coq (store_pos_int_pair_y_only : Z -> Z -> Z -> Assertion) */

/*@ include strategies "pos_int_pair.strategies" */
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_tutorial.pos_int_pair_lib */
