/*@ Extern Coq (sll :: *) */
/*@ Extern Coq
      (stack_capacity : Z)
      (sll_empty : sll)
      (sll_cons : Z -> sll -> sll)
      (sll_from_array : list Z -> sll)
      (store_stack : Z -> sll -> Z -> Assertion)
      (BuildStackPrefix : sll -> list Z -> Z -> Prop)
      (StackConcreteView : sll -> list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Data_structures.stack.stack_lib */

void push(int *stack, int n, int x)
/*@ With (before : sll)
    Require
      n < stack_capacity &&
      store_stack(stack, before, n) *
      IntArray::undef_seg(stack, n, n + 1)
    Ensure
      store_stack(stack, sll_cons(x, before), n + 1)
 */
{
  /*@ Assert
      exists concrete,
        stack == stack@pre && n == n@pre && x == x@pre &&
        0 <= n@pre && n@pre < stack_capacity &&
        StackConcreteView(before, concrete, n@pre) &&
        IntArray::full(stack, n@pre, concrete) *
        IntArray::undef_seg(stack, n@pre, n@pre + 1)
   */
  stack[n] = x;
  /*@ Assert
      stack == stack@pre && n == n@pre && x == x@pre &&
      0 <= n@pre && n@pre < stack_capacity &&
      store_stack(stack, sll_cons(x@pre, before), n@pre + 1)
   */
}

int pop(int *stack, int n)
/*@ With (top : Z) (rest : sll)
    Require
      1 <= n &&
      store_stack(stack, sll_cons(top, rest), n)
    Ensure
      __return == top &&
      store_stack(stack, rest, n - 1) *
      IntArray::undef_seg(stack, n - 1, n)
 */
{
  /*@ Assert
      exists concrete,
        stack == stack@pre && n == n@pre &&
        1 <= n@pre && n@pre <= stack_capacity &&
        StackConcreteView(
          sll_cons(top, rest), concrete, n@pre
        ) &&
        IntArray::full(stack, n@pre, concrete)
   */
  int ret = stack[n - 1];
  /*@ Assert
      stack == stack@pre && n == n@pre &&
      1 <= n@pre && n@pre <= stack_capacity &&
      ret == top &&
      store_stack(stack, rest, n@pre - 1) *
      IntArray::undef_seg(stack, n@pre - 1, n@pre)
   */
  return ret;
}

void build(int *stack, int n)
/*@ With (input : list Z)
    Require
      0 <= n &&
      n <= stack_capacity &&
      Zlength(input) == n &&
      IntArray::full(stack, n, input)
    Ensure
      store_stack(stack, sll_from_array(input), n)
 */
{
  /*@ Inv Assert
      (stack == stack@pre && n == n@pre &&
       n@pre == 0 && i == 1 &&
       Zlength(input) == n@pre &&
       IntArray::full(stack, n@pre, input))
      ||
      (exists prefix,
        stack == stack@pre && n == n@pre &&
        1 <= n@pre && n@pre <= stack_capacity &&
        1 <= i && i <= n@pre &&
        Zlength(input) == n@pre &&
        BuildStackPrefix(prefix, input, i) &&
        store_stack(stack, prefix, i) *
        IntArray::seg(stack, i, n@pre,
                      sublist(i, n@pre, input)))
   */
  for (int i = 1; i < n; ++i) {
    int x = stack[i];
    /*@ Assert
        exists prefix,
          stack == stack@pre && n == n@pre &&
          1 <= n@pre && n@pre <= stack_capacity &&
          1 <= i && i < n@pre &&
          x == input[i] &&
          Zlength(input) == n@pre &&
          BuildStackPrefix(prefix, input, i) &&
          store_stack(stack, prefix, i) *
          IntArray::undef_seg(stack, i, i + 1) *
          IntArray::seg(stack, i + 1, n@pre,
                        sublist(i + 1, n@pre, input))
     */
    push(stack, i, x);
    /*@ Assert
        exists next,
          stack == stack@pre && n == n@pre &&
          1 <= n@pre && n@pre <= stack_capacity &&
          1 <= i && i < n@pre &&
          x == input[i] &&
          Zlength(input) == n@pre &&
          BuildStackPrefix(next, input, i + 1) &&
          store_stack(stack, next, i + 1) *
          IntArray::seg(stack, i + 1, n@pre,
                        sublist(i + 1, n@pre, input))
     */
  }
  /*@ Assert
      stack == stack@pre && n == n@pre &&
      0 <= n@pre && n@pre <= stack_capacity &&
      Zlength(input) == n@pre &&
      store_stack(stack, sll_from_array(input), n@pre)
   */
}
