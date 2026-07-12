/*@ Extern Coq (Z::abs: Z -> Z) */

int delta(int x, int y)
/*@ Require
      0 <= x && x <= 100 &&
      0 <= y && y <= 100 &&
      emp
    Ensure
      __return == Z::abs(x - y) && emp
 */
{
    if (x < y) {
        return y - x;
    }
    else {
        return x - y;
    }
}
