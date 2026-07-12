int example(int x, int y) 
/*@ Require x < 50
    Ensure __return == 1 
*/
{
    y = 50;
    /*@ Inv
        neq: x <= 50 && y == 50;
        eq: x > 50 && x == y
        with
        all ==> neq
    */
    while (x < 100) {
        /*@ x >= INT_MIN by local $ neq */
        if (x < 50) {
            /*@ Branch clear eq */
            x++;
        } else {
            x++;
            y++;
            /*@ neq ==> eq */
        }
    }
    return x == y;
}


int unmatched(int x)
/*@ Require x == 0 || x == 1
    Ensure (__return == 1 && x == 0) || (__return == 0 && x == 1)
*/
{
  /*@ Branch name enter: x == 0; skip: x == 1 */
  /*@ Inv enter: x == 0 */
  while (x == 0) {
    return 1;
  }
  return 0;
}