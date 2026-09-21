#include "string.h"

/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (AlnumCode : Z -> Prop)
      (LongestPalindromeResult : list Z -> list Z -> Z -> Prop)
      (ManacherTransformedPrefix : list Z -> list Z -> Z -> Prop)
      (ManacherLoopState : list Z -> list Z -> Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (ExpansionLoopState : list Z -> list Z -> Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (OutputCopyPrefix : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (NonHashChars : list Z -> list Z)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.manacher.manacher_lib */

int longestPalindrom(char *s, int n, char *output)
/*@ With (str : list Z)
    Require
      valid_string(str) && Forall(AlnumCode, str) &&
      string_length(str) == n && 1 <= n && n <= 1000 &&
      store_string(s, str) * CharArray::undef_full(output, n + 1)
    Ensure
      exists out,
      LongestPalindromeResult(str, out, __return) &&
      store_string(s, str) *
      CharArray::full(output, __return + 1, app(out, cons(0, nil))) *
      CharArray::undef_seg(output, __return + 1, n + 1)
 */
{
    int i = 0;
    int j = 0;
    int len = 0;
    int id = 0;
    int limit = 0;
    int maxLen = 0;
    int maxId = 0;
    int r = 0;
    int mirror = 0;
    int ret = 0;
    char s2[2003];
    int p[2003];
    p[0] = 0;
    s2[0] = 36;
    /*@ Inv Assert
        exists s2_pre p_pre,
        Forall(AlnumCode, str) && string_length(str) == n@pre &&
        1 <= n@pre && n@pre <= 1000 && 0 <= i && i <= n@pre &&
        s == s@pre && output == output@pre && n == n@pre &&
        j == 0 && len == 0 && id == 0 && limit == 0 &&
        maxLen == 0 && maxId == 0 && r == 0 && mirror == 0 && ret == 0 &&
        ManacherTransformedPrefix(str, s2_pre, i) &&
        store_string(s@pre, str) *
        CharArray::undef_full(output@pre, n@pre + 1) *
        CharArray::seg(s2, 0, 2 * i + 1, s2_pre) *
        CharArray::undef_seg(s2, 2 * i + 1, 2003) *
        IntArray::seg(p, 0, 1, p_pre) * IntArray::undef_seg(p, 1, 2003)
    */
    while (i < n) {
        s2[2 * i + 1] = 35;
        s2[2 * i + 2] = s[i];
        i++;
    }
    s2[2 * i + 1] = 35;
    len = 2 * i + 2;
    s2[len] = 0;
    id = 0;
    limit = 0;
    maxLen = 0;
    maxId = 0;
    i = 1;
    /*@ Inv Assert
        exists s2_full p_cur,
        Forall(AlnumCode, str) && string_length(str) == n@pre &&
        1 <= n@pre && n@pre <= 1000 && len == 2 * n@pre + 2 &&
        1 <= i && i <= len && 0 <= id && id < i &&
        0 <= limit && limit <= len &&
        0 <= maxLen && maxLen <= n@pre && 0 <= maxId && maxId < len &&
        s == s@pre && output == output@pre && n == n@pre &&
        j == 0 && r == 0 && mirror == 0 && ret == 0 &&
        ManacherLoopState(str, s2_full, len, p_cur, i, id, limit, maxId, maxLen) &&
        store_string(s@pre, str) *
        CharArray::undef_full(output@pre, n@pre + 1) *
        CharArray::seg(s2, 0, len + 1, s2_full) *
        CharArray::undef_seg(s2, len + 1, 2003) *
        IntArray::seg(p, 0, i, p_cur) * IntArray::undef_seg(p, i, 2003)
     */
    while (i < len) {
        if (i < limit) {
            mirror = 2 * id - i;
            /*@ Assert
                exists s2_full p_cur,
                Forall(AlnumCode, str) && string_length(str) == n@pre &&
                1 <= n@pre && n@pre <= 1000 && len == 2 * n@pre + 2 &&
                1 <= i && i < len && 0 <= id && id < i &&
                0 <= mirror && mirror < i && mirror == 2 * id - i &&
                i < limit && limit <= len &&
                0 <= maxLen && maxLen <= n@pre && 0 <= maxId && maxId < len &&
                s == s@pre && output == output@pre && n == n@pre &&
                j == 0 && r == 0 && ret == 0 &&
                ManacherLoopState(str, s2_full, len, p_cur, i, id, limit, maxId, maxLen) &&
                store_string(s@pre, str) *
                CharArray::undef_full(output@pre, n@pre + 1) *
                CharArray::seg(s2, 0, len + 1, s2_full) *
                CharArray::undef_seg(s2, len + 1, 2003) *
                IntArray::seg(p, 0, i, p_cur) * IntArray::undef_seg(p, i, 2003)
             */
            if (p[mirror] < limit - i) {
                r = p[mirror];
                p[i] = r;
            } else {
                r = limit - i;
                p[i] = r;
            }
        } else {
            r = 1;
            p[i] = r;
        }
        /*@ Inv Assert
            exists s2_full p_written,
            Forall(AlnumCode, str) && string_length(str) == n@pre &&
            1 <= n@pre && n@pre <= 1000 && len == 2 * n@pre + 2 &&
            1 <= i && i < len && 1 <= r && 0 <= i - r && i + r <= len &&
            0 <= id && id < i && 0 <= limit && limit <= len &&
            0 <= maxLen && maxLen <= n@pre && 0 <= maxId && maxId < len &&
            s == s@pre && output == output@pre && n == n@pre &&
            j == 0 && ret == 0 && 0 <= mirror && mirror < len &&
            ExpansionLoopState(str, s2_full, len, p_written, i, r, id, limit, maxId, maxLen) &&
            store_string(s@pre, str) *
            CharArray::undef_full(output@pre, n@pre + 1) *
            CharArray::seg(s2, 0, len + 1, s2_full) *
            CharArray::undef_seg(s2, len + 1, 2003) *
            IntArray::seg(p, 0, i + 1, p_written) * IntArray::undef_seg(p, i + 1, 2003)
         */
        while (s2[i + r] == s2[i - r]) {

            r++;
            p[i] = r;
        }
        if (i + r > limit) {
            limit = i + r;
            id = i;
        }
        r = r - 1;
        if (maxLen < r) {
            maxLen = r;
            maxId = i;
        }
        r = 0;
        mirror = 0;
        i++;
    }
    j = 0;
    i = maxId - maxLen;
    /*@ Inv Assert
        exists s2_full p_done out_prefix,
        1 <= n@pre && n@pre <= 1000 && len == 2 * n@pre + 2 &&
        1 <= maxLen && maxLen <= n@pre &&
        0 <= maxId - maxLen && maxId + maxLen < len &&
        maxId - maxLen <= i && i <= maxId + maxLen + 1 &&
        0 <= j && j <= maxLen &&
        0 <= id && id < len && 0 <= limit && limit <= len &&
        r == 0 && mirror == 0 && ret == 0 &&
        OutputCopyPrefix(s2_full, out_prefix, maxId - maxLen, i, j) &&
        LongestPalindromeResult(str,
            NonHashChars(sublist(maxId - maxLen, maxId + maxLen + 1, s2_full)), maxLen) &&
        s == s@pre && output == output@pre && n == n@pre &&
        store_string(s@pre, str) *
        CharArray::full(output@pre, j, out_prefix) *
        CharArray::undef_seg(output@pre, j, n@pre + 1) *
        CharArray::seg(s2, 0, len + 1, s2_full) *
        CharArray::undef_seg(s2, len + 1, 2003) *
        IntArray::seg(p, 0, len, p_done) * IntArray::undef_seg(p, len, 2003)
     */
    while (i <= maxId + maxLen) {
        if (s2[i] != 35) {
            output[j] = s2[i];
            j++;
        }
        i++;
    }
    /* The completed local arrays must be consolidated before QCP releases them. */
    /*@ Assert
        exists out_prefix,
        j == maxLen && 1 <= maxLen && maxLen <= n@pre && n@pre <= 1000 &&
        i == maxId + maxLen + 1 && len == 2 * n@pre + 2 &&
        0 <= id && id < len && 0 <= limit && limit <= len &&
        r == 0 && mirror == 0 && ret == 0 &&
        s == s@pre && output == output@pre && n == n@pre &&
        LongestPalindromeResult(str, out_prefix, maxLen) &&
        store_string(s@pre, str) *
        CharArray::full(output@pre, j, out_prefix) *
        CharArray::undef_seg(output@pre, j, n@pre + 1) *
        CharArray::undef_full(s2, 2003) * IntArray::undef_full(p, 2003)
     */
    output[j] = 0;
    ret = maxLen;
    return ret;
}
