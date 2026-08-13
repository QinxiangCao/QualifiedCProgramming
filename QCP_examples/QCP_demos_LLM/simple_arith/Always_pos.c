

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.simple_arith.Apos_lib */
/*@ Import Lean import SimpleC.EE.QCP_demos_LLM.simple_arith.Apos_lib */

/*@ Extern Coq (Always_pos: Z -> Z -> Z -> Z) */

int Always_positive_simple(int a,int b, int c)
/*@ Require
        INT_MIN < a && a <= INT_MAX &&
        INT_MIN < b && b <= INT_MAX &&
        INT_MIN < c && c <= INT_MAX && emp
      Ensure
        __return == Always_pos(a,b,c) && emp
   */
{
  if (a == 0) {
    return 0;
  } else {
    long long delta1, delta2;
    delta1 = (long long) b * (long long) b / (long long) 4;
    delta2 = (long long) a * (long long) c;
    if (delta1 >= delta2) {
      return 0; 
    } else {
      if (a > 0) {
        return 1;
      } else {
        return 0;
      }
    }
  }
}

int Always_positive(int a,int b, int c)
  /*@ Require
        INT_MIN < a && a <= INT_MAX &&
        INT_MIN < b && b <= INT_MAX &&
        INT_MIN < c && c <= INT_MAX && emp
      Ensure
        __return == Always_pos(a,b,c) && emp
   */
{
  if (a == 0) {
    return 0;
  } else {
    long long delta0, delta1, delta2;
    int d;
    delta0 = (long long) b * (long long) b;
    delta1 = delta0;
    delta2 = (long long) a * (long long) c;
    if (delta2 <= (long long) 0) {
      d = 0;
    }
    else {
      d = 4;
      /*@ Inv Assert
          0 < d && d <= 4 &&
          INT_MIN < a@pre && a@pre <= INT_MAX &&
          INT_MIN < b@pre && b@pre <= INT_MAX &&
          INT_MIN < c@pre && c@pre <= INT_MAX &&
          0 < a@pre * c@pre &&
          delta0 == b@pre * b@pre && delta2 == a@pre * c@pre && delta0 == delta1 + (4 - d) * delta2 &&
          a == a@pre && b == b@pre && c == c@pre
      */
      while (delta2 <= delta1) {
        delta1 = delta1 - delta2;
        d = d - 1;
        if (d == 0) {
          if (delta1 >= (long long)0) {
            d = 0;
          } else {
            d = 1;
          }
          break;
        }
      }
    }
    if (d == 0) {
      return 0;
    } else {
      if (a > 0) {
        return 1;
      } else {
        return 0;
      }
    }
  }
}
