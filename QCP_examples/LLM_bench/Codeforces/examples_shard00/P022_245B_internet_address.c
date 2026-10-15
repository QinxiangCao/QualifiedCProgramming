/* Codeforces 245/B - Internet Address */
// #include <stdio.h>
#include "string.h"

/* QCP_INSERT_BEGIN:P022_245B_internet_address.support */
/*@ Extern Coq
      (Pre : list Z -> Prop)
      (Spec : list Z -> list Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (CharArray::undef_full : Z -> Z -> Assertion)
      (CharArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Extern Coq (CharArray::seg : Z -> Z -> Z -> list Z -> Assertion) */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P022_245B_internet_address_lib */
/* QCP_INSERT_END:P022_245B_internet_address.support */
static void solver(const char *s,
                   char *out) /* QCP_INSERT_BEGIN:P022_245B_internet_address.contract */

/*@ With (plain : list Z)
    Require
      1 <= Zlength(plain) && Zlength(plain) <= 50 &&
      (forall i, (0 <= i && i < Zlength(plain)) => (97 <= plain[i] && plain[i] <= 122)) &&
      Pre(plain) &&
      CharArray::full(s, Zlength(plain) + 1, app(plain, cons(0, nil))) *
      CharArray::undef_full(out, 72)
    Ensure
      exists address,
        Spec(plain, address) &&
        CharArray::full(s, Zlength(plain) + 1, app(plain, cons(0, nil))) *
        CharArray::full(out, Zlength(address) + 1, app(address, cons(0, nil))) *
        CharArray::undef_seg(out, Zlength(address) + 1, 72)
*/
/* QCP_INSERT_END:P022_245B_internet_address.contract */

{
    /*@ Assert
        s == s@pre && out == out@pre &&
        1 <= Zlength(plain) && Zlength(plain) <= 50 &&
        Pre(plain) &&
        valid_string(plain) &&
        string_length(plain) == Zlength(plain) &&
        string_length(plain) < INT_MAX &&
        store_string(s, plain) *
        CharArray::undef_full(out, 72)
    */
    int n = (int)strlen(s) /*@ where str = plain */, p = s[0] == 'h' ? 4 : 3, ru = -1, k = 0;
    /*@ Inv Assert
      exists marker,
        s == s@pre && out == out@pre &&
        n == Zlength(plain) &&
        1 <= n && n <= 50 &&
        Pre(plain) &&
        ((p == 4 &&
          sublist(0, p, plain) == cons(104, cons(116, cons(116, cons(112, nil))))) ||
         (p == 3 &&
          sublist(0, p, plain) == cons(102, cons(116, cons(112, nil))))) &&
        p + 1 <= i && i <= marker &&
        marker + 1 < n &&
        plain[marker] == 114 && plain[marker + 1] == 117 &&
        ru == -1 && k == 0 &&
        CharArray::full(s, n + 1, app(plain, cons(0, nil))) *
        CharArray::undef_full(out, 72)
    */
    for (int i = p + 1; i + 1 < n; ++i)
        if (s[i] == 'r' && s[i + 1] == 'u')
        {
            ru = i;
            break;
        }
    /*@ Assert
        s == s@pre && out == out@pre &&
        n == Zlength(plain) &&
        1 <= n && n <= 50 &&
        Pre(plain) &&
        ((p == 4 &&
          sublist(0, p, plain) == cons(104, cons(116, cons(116, cons(112, nil))))) ||
         (p == 3 &&
          sublist(0, p, plain) == cons(102, cons(116, cons(112, nil))))) &&
        p + 1 <= ru && ru + 1 < n &&
        plain[ru] == 114 && plain[ru + 1] == 117 &&
        k == 0 &&
        CharArray::full(s, n + 1, app(plain, cons(0, nil))) *
        CharArray::undef_full(out, 72)
    */
    /*@ Inv Assert
        s == s@pre && out == out@pre &&
        n == Zlength(plain) &&
        1 <= n && n <= 50 &&
        Pre(plain) &&
        ((p == 4 &&
          sublist(0, p, plain) == cons(104, cons(116, cons(116, cons(112, nil))))) ||
         (p == 3 &&
          sublist(0, p, plain) == cons(102, cons(116, cons(112, nil))))) &&
        p + 1 <= ru && ru + 1 < n &&
        plain[ru] == 114 && plain[ru + 1] == 117 &&
        0 <= i && i <= p && k == i &&
        CharArray::full(s, n + 1, app(plain, cons(0, nil))) *
        CharArray::seg(out, 0, k, sublist(0, i, plain)) *
        CharArray::undef_seg(out, k, 72)
    */
    for (int i = 0; i < p; ++i)
    {
        out[k] = s[i];
        k++;
    }
    out[k] = ':';
    k++;
    out[k] = '/';
    k++;
    out[k] = '/';
    k++;
    /*@ Assert
        s == s@pre && out == out@pre &&
        n == Zlength(plain) &&
        1 <= n && n <= 50 &&
        Pre(plain) &&
        ((p == 4 &&
          sublist(0, p, plain) == cons(104, cons(116, cons(116, cons(112, nil))))) ||
         (p == 3 &&
          sublist(0, p, plain) == cons(102, cons(116, cons(112, nil))))) &&
        p + 1 <= ru && ru + 1 < n &&
        plain[ru] == 114 && plain[ru + 1] == 117 &&
        k == p + 3 &&
        CharArray::full(s, n + 1, app(plain, cons(0, nil))) *
        CharArray::seg(out, 0, k,
          app(sublist(0, p, plain),
              cons(58, cons(47, cons(47, nil))))) *
        CharArray::undef_seg(out, k, 72)
    */
    /*@ Inv Assert
        s == s@pre && out == out@pre &&
        n == Zlength(plain) &&
        1 <= n && n <= 50 &&
        Pre(plain) &&
        ((p == 4 &&
          sublist(0, p, plain) == cons(104, cons(116, cons(116, cons(112, nil))))) ||
         (p == 3 &&
          sublist(0, p, plain) == cons(102, cons(116, cons(112, nil))))) &&
        p + 1 <= ru && ru + 1 < n &&
        plain[ru] == 114 && plain[ru + 1] == 117 &&
        p <= i && i <= ru && k == i + 3 &&
        CharArray::full(s, n + 1, app(plain, cons(0, nil))) *
        CharArray::seg(out, 0, k,
          app(sublist(0, p, plain),
              app(cons(58, cons(47, cons(47, nil))),
                  sublist(p, i, plain)))) *
        CharArray::undef_seg(out, k, 72)
    */
    for (int i = p; i < ru; ++i)
    {
        out[k] = s[i];
        k++;
    }
    out[k] = '.';
    k++;
    out[k] = 'r';
    k++;
    out[k] = 'u';
    k++;
    /*@ Assert
        s == s@pre && out == out@pre &&
        n == Zlength(plain) &&
        1 <= n && n <= 50 &&
        Pre(plain) &&
        ((p == 4 &&
          sublist(0, p, plain) == cons(104, cons(116, cons(116, cons(112, nil))))) ||
         (p == 3 &&
          sublist(0, p, plain) == cons(102, cons(116, cons(112, nil))))) &&
        p + 1 <= ru && ru + 1 < n &&
        plain[ru] == 114 && plain[ru + 1] == 117 &&
        k == ru + 6 &&
        CharArray::full(s, n + 1, app(plain, cons(0, nil))) *
        CharArray::seg(out, 0, k,
          app(sublist(0, p, plain),
              app(cons(58, cons(47, cons(47, nil))),
                  app(sublist(p, ru, plain),
                      cons(46, cons(114, cons(117, nil))))))) *
        CharArray::undef_seg(out, k, 72)
    */
    if (ru + 2 < n)
    {
        out[k] = '/';
        k++;
        /*@ Inv Assert
            s == s@pre && out == out@pre &&
            n == Zlength(plain) &&
            1 <= n && n <= 50 &&
            Pre(plain) &&
            ((p == 4 &&
              sublist(0, p, plain) == cons(104, cons(116, cons(116, cons(112, nil))))) ||
             (p == 3 &&
              sublist(0, p, plain) == cons(102, cons(116, cons(112, nil))))) &&
            p + 1 <= ru && ru + 2 < n &&
            plain[ru] == 114 && plain[ru + 1] == 117 &&
            ru + 2 <= i && i <= n && k == i + 5 &&
            CharArray::full(s, n + 1, app(plain, cons(0, nil))) *
            CharArray::seg(out, 0, k,
              app(sublist(0, p, plain),
                  app(cons(58, cons(47, cons(47, nil))),
                      app(sublist(p, ru, plain),
                          app(cons(46, cons(114, cons(117, nil))),
                              app(cons(47, nil), sublist(ru + 2, i, plain))))))) *
            CharArray::undef_seg(out, k, 72)
        */
        for (int i = ru + 2; i < n; ++i)
        {
            out[k] = s[i];
            k++;
        }
    }
    /*@ Assert
        exists address,
          s == s@pre && out == out@pre &&
          n == Zlength(plain) &&
          1 <= n && n <= 50 &&
          Pre(plain) &&
          (p == 3 || p == 4) &&
          p + 1 <= ru && ru + 1 < n &&
          Spec(plain, address) &&
          k == Zlength(address) &&
          0 <= k && k < 72 &&
          CharArray::full(s, n + 1, app(plain, cons(0, nil))) *
          CharArray::seg(out, 0, k, address) *
          CharArray::undef_seg(out, k, 72)
    */
    out[k] = '\0';
}

// int main(void)
// {
//     char s[64], out[72];
//     if (scanf("%63s", s) != 1) return 0;
//     solver(s, out); puts(out);
//     return 0;
// }
