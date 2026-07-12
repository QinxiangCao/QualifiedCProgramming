/*@ Import Coq Require Import SimpleC.EE.QCP_demos_tutorial.branch_join_private_condition_lib */

/*@ Extern Coq (step: Z -> Z) */

int f(int x)
/*@ Require x > 0 && x <= 715827882
    Ensure __return == 0
*/
{
  if (x % 2 == 0) {
    x = x / 2;
  } else {
    x = 3 * x + 1;
  }
  /*@ Branch join all with x == step(x@pre) */
  return 0;
}
