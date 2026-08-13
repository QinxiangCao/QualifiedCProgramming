



#include "safeexecE_def.h"

/*@ Extern Coq (ATrue: {A} -> A -> Prop)
               (inner_loop: {A} -> A -> list A -> list Z -> A -> Z -> program unit Z)
               (constr_loop: {A} -> A -> list A -> program unit (list Z))
               (match_loop: {A} -> A -> list A -> list A -> list Z -> program unit (option Z))
               (is_prefix_func: {A} -> list Z -> list A -> Prop)
               (no_occurance: {A} -> list A -> list A -> Prop)
               (first_occur: {A} -> list A -> list A -> Z -> Prop)
               (option_int_repr: (option Z) -> Z)
               (constr_loop_from: {A} -> A -> list A -> Z -> list Z -> Z -> program unit (list Z))
               (constr_loop_from_after: {A} -> A -> list A -> Z -> list Z -> Z -> program unit (list Z))
               (match_loop_from: {A} -> A -> list A -> list A -> list Z -> Z -> Z -> program unit (option Z))
               (match_loop_from_after: {A} -> A -> list A -> list A -> list Z -> Z -> Z -> program unit (option Z))
                */

/*@ Extern Coq (constr_loop_from: {A} -> A -> list A -> Z -> list Z -> Z -> program unit (list Z))*/

/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.kmp_rel_lib */
/*@ Import Lean import SimpleC.EE.QCP_demos_LLM.kmp_rel_lib */

int * malloc_int_array(int n)
  /*@ Require n > 0 && emp
      Ensure exists l, IntArray::full(__return, n, l)
   */
  ;

void free_int_array(int *a)
  /*@ With n l
      Require IntArray::full(a, n, l)
      Ensure emp
   */
  ;

int strlen(char * s)
  /*@ With l n
      Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
      Ensure  __return == n &&
              CharArray::full(s, n + 1, app(l, cons(0, nil)))
   */
  ;

int inner(char *str, int *vnext, char ch, int j)
/*@ bind_spec <= low_level_spec
    With {B} str0 vnext0 n m X (f: Z -> program unit B)
    Require safeExec(ATrue, bind(inner_loop(0, str0, vnext0, ch, j), f), X) &&
            m <= n && n < INT_MAX &&
            CharArray::full(str, n + 1, app(str0, cons(0, nil))) *
            IntArray::full(vnext, m, vnext0)
    Ensure safeExec(ATrue, applyf(f, __return), X) && 0 <= __return && __return < m + 1 &&
           CharArray::full(str, n + 1, app(str0, cons(0, nil))) *
           IntArray::full(vnext, m, vnext0)
*/;

int inner(char *str, int *vnext, char ch, int j) 
/*@ low_level_spec
    With str0 vnext0 n m X
    Require safeExec(ATrue, inner_loop(0, str0, vnext0, ch, j), X) &&
            m <= n && n < INT_MAX &&
            CharArray::full(str, n + 1, app(str0, cons(0, nil))) *
            IntArray::full(vnext, m, vnext0)
    Ensure safeExec(ATrue, return(__return), X) && 0 <= __return && __return < m + 1 &&
           CharArray::full(str, n + 1, app(str0, cons(0, nil))) *
           IntArray::full(vnext, m, vnext0) 
*/
{
    /*@ Inv 
        safeExec(ATrue, inner_loop(0, str0, vnext0, ch, j), X) && 
        str == str@pre && vnext == vnext@pre &&
        CharArray::full(str, n + 1, app(str0, cons(0, nil))) *
        IntArray::full(vnext, m, vnext0)
    */
    while (1) {
        /*@
            0 <= j && j < m 
        */
        if (str[j] == ch) return j + 1;
        if (j == 0) return 0;
        j = vnext[j-1];
    }
}

int * constr(char *patn)
  /*@ high_level_spec <= low_level_spec
      With str n
      Require n > 0 && n < INT_MAX && CharArray::full(patn, n + 1, app(str, cons(0, nil)))
      Ensure exists vnext,
               is_prefix_func(vnext, str) && 
               IntArray::full(__return, n, vnext) *
               CharArray::full(patn, n + 1, app(str, cons(0, nil)))
  */
;

int * constr(char *patn) 
  /*@ low_level_spec
      With str n X
      Require safeExec(ATrue, constr_loop(0, str), X) && n > 0 && n < INT_MAX &&
              CharArray::full(patn, n + 1, app(str, cons(0, nil)))
      Ensure exists (vnext: list Z),
               safeExec(ATrue, return(vnext), X) &&
               IntArray::full(__return, n, vnext) *
               CharArray::full(patn, n + 1, app(str, cons(0, nil)))
  */
{
    int len = strlen(patn) /*@ where l = str, n = n*/;
    int *vnext = malloc_int_array(len);
    vnext[0] = 0;
    int j = 0;
    int i = 1;
        /*@ Inv Assert
                exists vnext0 l0,
                    safeExec(ATrue, constr_loop_from(0, str, i, vnext0, j), X) &&
                    patn == patn@pre &&
                    len == n && n < INT_MAX && 1 <= i &&
                    CharArray::full(patn, n + 1, app(str, cons(0, nil))) *
                    IntArray::full(vnext, i, vnext0) *
                    IntArray::full((vnext + i * sizeof(int)), n - i, l0)
        */
    for (; i < len; i++) {
        /*@ Given vnext0 l0 */
        j = inner(patn, vnext, patn[i], j) 
          /*@ where (bind_spec) str0 = str, vnext0 = vnext0, m = i, n = n, 
              X = X, f = constr_loop_from_after(0, str, i, vnext0); B = list Z */;
        /*@ Assert 
            exists l, 
             safeExec(ATrue, constr_loop_from_after(0, str, i, vnext0, j), X) &&
             patn == patn@pre &&
             len == n && n < INT_MAX && 1 <= i && i < len &&
             l == app(vnext0, l0) && Zlength(vnext0) == i &&
             0 <= j && j < i + 1 &&
             CharArray::full(patn, n + 1, app(str, cons(0, nil))) *
             IntArray::full(vnext, n, l)
        */
        vnext[i] = j;
    }
    return vnext;
}

int match(char *patn, char *text, int *vnext)
/*@ high_level_spec <= low_level_spec
    With patn0 text0 vnext0 n m
    Require is_prefix_func(vnext0, patn0) && n > 0 && n < INT_MAX && m < INT_MAX &&
            CharArray::full(patn, n + 1, app(patn0, cons(0, nil))) *
            CharArray::full(text, m + 1, app(text0, cons(0, nil))) *
            IntArray::full(vnext, n, vnext0)
    Ensure ((__return >= 0 && first_occur(patn0, text0, __return)) ||
            (__return == -1 && no_occurance(patn0, text0))) &&
            CharArray::full(patn, n + 1, app(patn0, cons(0, nil))) *
            CharArray::full(text, m + 1, app(text0, cons(0, nil))) *
            IntArray::full(vnext, n, vnext0)
*/
;

int match(char *patn, char *text, int *vnext)
/*@ low_level_spec
    With patn0 text0 vnext0 n m X
    Require safeExec(ATrue, match_loop(0, patn0, text0, vnext0), X) && 
            n > 0 && n < INT_MAX && m < INT_MAX &&
            CharArray::full(patn, n + 1, app(patn0, cons(0, nil))) *
            CharArray::full(text, m + 1, app(text0, cons(0, nil))) *
            IntArray::full(vnext, n, vnext0)
    Ensure exists ret,
             safeExec(ATrue, return(ret), X) && __return == option_int_repr(ret) &&
             CharArray::full(patn, n + 1, app(patn0, cons(0, nil))) *
             CharArray::full(text, m + 1, app(text0, cons(0, nil))) *
             IntArray::full(vnext, n, vnext0)
*/
{
    int j = 0;
    int text_len = strlen(text) /*@ where l = text0, n = m*/;
    int patn_len = strlen(patn) /*@ where l = patn0, n = n*/;
    int i = 0;
    /*@ Inv Assert
        safeExec(ATrue, match_loop_from(0, patn0, text0, vnext0, i, j), X) &&
        vnext == vnext@pre && text == text@pre && patn == patn@pre &&
        text_len == m && patn_len == n &&
        n < INT_MAX && m < INT_MAX && i >= 0 &&
        CharArray::full(patn, n + 1, app(patn0, cons(0, nil))) *
        CharArray::full(text, m + 1, app(text0, cons(0, nil))) *
        IntArray::full(vnext, n, vnext0)
    */
    for (; i < text_len; i++) {
      j = inner(patn, vnext, text[i], j)
          /*@ where (bind_spec) str0 = patn0, vnext0 = vnext0, m = n, n = n,
              X = X, f = match_loop_from_after(0, patn0, text0, vnext0, i) ; B = option Z*/
          ;
      if (j == patn_len)
      {
        return i - patn_len + 1;
        }
    }
    return -1;
}

int main(char *patn, char *text)
/*@ 
    With patn0 text0 n m
    Require n > 0 && n < INT_MAX && m < INT_MAX &&
            CharArray::full(patn, n + 1, app(patn0, cons(0, nil))) *
            CharArray::full(text, m + 1, app(text0, cons(0, nil)))
    Ensure ((__return >= 0 && first_occur(patn0, text0, __return)) ||
            (__return == -1 && no_occurance(patn0, text0))) &&
            CharArray::full(patn, n + 1, app(patn0, cons(0, nil))) *
            CharArray::full(text, m + 1, app(text0, cons(0, nil)))
*/
{
    int *vnext = constr(patn) /*@ where (high_level_spec) str = patn0, n = n */;
    /*@ Assert exists vnext0,
            is_prefix_func(vnext0, patn0) &&
            n > 0 && n < INT_MAX && m < INT_MAX &&
            patn == patn@pre && text == text@pre &&
            CharArray::full(patn, n + 1, app(patn0, cons(0, nil))) *
            CharArray::full(text, m + 1, app(text0, cons(0, nil))) *
            IntArray::full(vnext, n, vnext0)
    */
    /*@ Given vnext0 */
    int r = match(patn, text, vnext)
        /*@ where (high_level_spec) patn0 = patn0, text0 = text0, vnext0 = vnext0, n = n, m = m */;
    free_int_array(vnext) /*@ where n = n, l = vnext0 */;
    return r;
}
