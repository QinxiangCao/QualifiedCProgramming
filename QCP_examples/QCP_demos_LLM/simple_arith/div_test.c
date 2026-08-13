

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.simple_arith.PDiv_lib */
/*@ Import Lean import SimpleC.EE.QCP_demos_LLM.simple_arith.PDiv_lib */

/*@ Extern Coq (Pos_Div : Z -> Z -> Z -> Z) */

long long div_test(int a,int b, int c)
  /*@ Require
        INT_MIN < a && a <= INT_MAX &&
        INT_MIN < b && b <= INT_MAX &&
        INT_MIN < c && c <= INT_MAX
      Ensure
        __return == Pos_Div(a*b,c,0)
   */
{
  if (c == 0) {
    return (long long)0;
  } else {
    long long d;
    d = (long long)a * (long long)b / (long long) c;
    if (d < (long long) 0) return (long long)0;
    return d;
  }
}
