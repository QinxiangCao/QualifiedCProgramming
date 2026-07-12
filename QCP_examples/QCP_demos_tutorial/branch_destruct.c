
int example(int x, int y) 
/*@ Require x < 50
    Ensure (x == y && __return == 1) || (x != y && __return == 0) 
*/
{
  /*@ Destruct $ all with
      Less : x < y;
      Eq : x == y;
      Greater: x > y
  */

  /*@ Destruct $ Less with 
      Less25 : x < 25;
      Less50 : x < 50
  */
  return x == y;
}
