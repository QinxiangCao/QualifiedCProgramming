int bounded_power_of_two()
/*@ Require emp
    Ensure exists t, 0 < t && t < 10 && __return == (1 << (t + 2)) */
{
  return 32;
}

int given_of_marked_call()
/*@ Require emp
    Ensure exists u, __return == (1 << u) && u >= 2 */
{
  int x = bounded_power_of_two() /*@ where @mark call_x */;
  //@ Given t of call_x
  //@ x == 1 << (t + 2)
  //@ exists u, x == (1 << u) && u >= 2
  return x;
}

int given_from_of_two_marked_calls()
/*@ Require emp
    Ensure emp */
{
  int first = bounded_power_of_two() /*@ where @mark first_call */;
  int second = bounded_power_of_two() /*@ where @mark second_call */;

  //@ Given first_t from t of first_call
  //@ Given second_t from t of second_call
  //@ first == 1 << (first_t + 2)
  //@ second == 1 << (second_t + 2)

  return first + second;
}
