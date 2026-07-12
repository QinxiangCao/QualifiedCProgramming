struct int_pair {
    int a;
    int b;
};

/*@ Extern Coq (store_int_pair : Z -> Z -> Z -> Assertion) */
/*@ include strategies "swap_simple2.strategies" */
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_tutorial.swap_simple1_lib */
