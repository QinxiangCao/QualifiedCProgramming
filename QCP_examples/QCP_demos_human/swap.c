void swap(int * px, int * py)
/*@ neq 
    With x y
    Require x == *px && y == *py
    Ensure  y == *px && x == *py
*/
/*@ eq
    With x
    Require px == py && x == *px
    Ensure x == *px
*/;

void swap(int * px, int * py)
/*@ eq */
/*@ neq */
{
  int t;
  t = * px;
  * px = * py;
  * py = t;
}              

void swap_test1(int *x, int *y) 
/*@ 
   Require x != y && *x == 1 && *y == 2
   Ensure  *y == 1 && *x == 2
*/
{
  swap(x, y) /*@ where (neq) */;
}

void swap_test2(int *x, int *y) 
/*@ 
   Require x == y && *x == 1
   Ensure  *y == 1
*/
{
  swap(x, y) /*@ where (eq) */;
}