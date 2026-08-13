
#include "char_array_def.h"

/*@ Import Coq Require Import SimpleC.StdLib.string_lib */

/*@ Extern Coq (store_string : Z -> list Z -> Assertion)
               (all_ascii : list Z -> Prop)
               (no_inner_nul : list Z -> Prop)
               (valid_string : list Z -> Prop)
               (c_string : list Z -> list Z)
               (string_length : list Z -> Z)
               (memchr_result : list Z -> Z -> Z -> Z -> Z -> Prop)
               (strchr_result : list Z -> Z -> Z -> Z -> Prop)
               (strcmp_result : list Z -> list Z -> Z -> Prop)
               (strncmp_result : list Z -> list Z -> Z -> Z -> Prop)
               (strncpy_content : list Z -> Z -> list Z -> Prop)
               (strncat_result : list Z -> list Z -> Z -> list Z -> Prop)
 */

/*@ include strategies "string.strategies" */

int strlen(char *s)
/*@ With str
    Require valid_string(str) && string_length(str) < INT_MAX && store_string(s, str)
    Ensure __return == string_length(str) && store_string(s, str)
*/
;

char *memcpy(char *dest, char *src, int n)
/*@ With bytes
    Require all_ascii(bytes) && Zlength(bytes) == n &&
            0 <= n && n < INT_MAX &&
            CharArray::undef_full(dest, n) * CharArray::full(src, n, bytes)
    Ensure __return == dest &&
           CharArray::full(dest, n, bytes) * CharArray::full(src, n, bytes)
*/
;

char *memmove(char *dest, char *src, int n)
/*@ With bytes
    Require all_ascii(bytes) && Zlength(bytes) == n &&
            0 <= n && n < INT_MAX &&
            CharArray::undef_full(dest, n) * CharArray::full(src, n, bytes)
    Ensure __return == dest &&
           CharArray::full(dest, n, bytes) * CharArray::full(src, n, bytes)
*/
;

char *memset(char *s, int c, int n)
/*@ Require 0 <= n && n < INT_MAX &&
            0 <= c && c <= 127 &&
            CharArray::undef_full(s, n)
    Ensure __return == s && CharArray::full(s, n, repeat_Z(c, n))
*/
;

char *memchr(char *s, int c, int n)
/*@ With bytes
    Require all_ascii(bytes) && Zlength(bytes) == n &&
            0 <= c && c <= 127 &&
            0 <= n && n < INT_MAX &&
            CharArray::full(s, n, bytes)
    Ensure memchr_result(bytes, c, n, __return, s) &&
           CharArray::full(s, n, bytes)
*/
;

char *strchr(char *s, int c)
/*@ With str
    Require valid_string(str) &&
            0 <= c && c <= 127 &&
            string_length(str) < INT_MAX &&
            store_string(s, str)
    Ensure strchr_result(str, c, __return, s) && store_string(s, str)
*/
;

int strcmp(char *s1, char *s2)
/*@ With str1 str2
    Require valid_string(str1) && valid_string(str2) &&
            string_length(str1) < INT_MAX && string_length(str2) < INT_MAX &&
            store_string(s1, str1) * store_string(s2, str2)
    Ensure strcmp_result(str1, str2, __return) &&
           store_string(s1, str1) * store_string(s2, str2)
*/
;

int strncmp(char *s1, char *s2, int n)
/*@ With str1 str2
    Require valid_string(str1) && valid_string(str2) &&
            0 <= n && n < INT_MAX &&
            string_length(str1) < INT_MAX && string_length(str2) < INT_MAX &&
            store_string(s1, str1) * store_string(s2, str2)
    Ensure strncmp_result(str1, str2, n, __return) &&
           store_string(s1, str1) * store_string(s2, str2)
*/
;

char *strcpy(char *dest, char *src)
/*@ With src_str
    Require valid_string(src_str) &&
            string_length(src_str) < INT_MAX &&
            CharArray::undef_full(dest, string_length(src_str) + 1) *
            store_string(src, src_str)
    Ensure __return == dest &&
           store_string(dest, src_str) * store_string(src, src_str)
*/
;

char *strncpy(char *dest, char *src, int n)
/*@ With src_str
    Require valid_string(src_str) &&
            0 <= n && n < INT_MAX &&
            CharArray::undef_full(dest, n) *
            store_string(src, src_str)
    Ensure exists out,
             strncpy_content(src_str, n, out) &&
             __return == dest &&
             CharArray::full(dest, n, out) * store_string(src, src_str)
*/
;

char *strcat(char *dest, char *src)
/*@ With dst_str src_str
    Require valid_string(dst_str) && valid_string(src_str) &&
            string_length(dst_str) + string_length(src_str) + 1 < INT_MAX &&
            store_string(dest, dst_str) *
            CharArray::undef_seg(dest, string_length(dst_str) + 1,
                                      string_length(dst_str) + string_length(src_str) + 1) *
            store_string(src, src_str)
    Ensure __return == dest &&
           store_string(dest, app(dst_str, src_str)) *
           store_string(src, src_str)
*/
;

char *strncat(char *dest, char *src, int n)
/*@ With dst_str src_str
    Require valid_string(dst_str) && valid_string(src_str) &&
            0 <= n && n < INT_MAX &&
            string_length(dst_str) + n + 1 < INT_MAX &&
            store_string(dest, dst_str) *
            CharArray::undef_seg(dest, string_length(dst_str) + 1,
                                      string_length(dst_str) + n + 1) *
            store_string(src, src_str)
    Ensure exists out,
             strncat_result(dst_str, src_str, n, out) &&
             __return == dest &&
             store_string(dest, out) *
             CharArray::undef_seg(dest, string_length(out) + 1,
                                  string_length(dst_str) + n + 1) *
             store_string(src, src_str)
*/
;
