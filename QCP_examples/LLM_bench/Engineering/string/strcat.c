#include "string.h"

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
{
  int i = 0;
  /*@ Inv Assert
      valid_string(dst_str) && valid_string(src_str) &&
      string_length(dst_str) + string_length(src_str) + 1 < INT_MAX &&
      0 <= i && i <= string_length(dst_str) &&
      dest == dest@pre && src == src@pre &&
      (forall (k: Z), (0 <= k && k < i) => Znth(k, dst_str, 0) != 0) &&
      store_string(dest@pre, dst_str) *
      CharArray::undef_seg(dest@pre, string_length(dst_str) + 1,
                                     string_length(dst_str) + string_length(src_str) + 1) *
      store_string(src@pre, src_str)
  */
  while (dest[i] != 0) {
    i++;
  }

  int j = 0;
  /*@ Inv Assert
      valid_string(dst_str) && valid_string(src_str) &&
      string_length(dst_str) + string_length(src_str) + 1 < INT_MAX &&
      i == string_length(dst_str) &&
      0 <= j && j <= string_length(src_str) &&
      dest == dest@pre && src == src@pre &&
      CharArray::full(dest@pre, string_length(dst_str) + j,
                      app(dst_str, sublist(0, j, src_str))) *
      store(dest@pre + (string_length(dst_str) + j) * sizeof(char), char, 0) *
      CharArray::undef_seg(dest@pre, string_length(dst_str) + j + 1,
                                     string_length(dst_str) + string_length(src_str) + 1) *
      store_string(src@pre, src_str)
  */
  while (src[j] != 0) {
    /*@ Assert
        valid_string(dst_str) && valid_string(src_str) &&
        string_length(dst_str) + string_length(src_str) + 1 < INT_MAX &&
        i == string_length(dst_str) &&
        0 <= j && j < string_length(src_str) &&
        dest == dest@pre && src == src@pre &&
        CharArray::full(dest@pre, string_length(dst_str) + j,
                        app(dst_str, sublist(0, j, src_str))) *
        store(dest@pre + (string_length(dst_str) + j) * sizeof(char), char, 0) *
        CharArray::undef_seg(dest@pre, string_length(dst_str) + j + 1,
                                       string_length(dst_str) + string_length(src_str) + 1) *
        store_string(src@pre, src_str)
    */
    dest[i + j] = src[j];
    j++;
    dest[i + j] = 0;
  }
  return dest;
}

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
{
  int i = 0;
  /*@ Inv Assert
      valid_string(dst_str) && valid_string(src_str) &&
      0 <= n@pre && n@pre < INT_MAX &&
      string_length(dst_str) + n@pre + 1 < INT_MAX &&
      0 <= i && i <= string_length(dst_str) &&
      dest == dest@pre && src == src@pre && n == n@pre &&
      (forall (k: Z), (0 <= k && k < i) => Znth(k, dst_str, 0) != 0) &&
      store_string(dest@pre, dst_str) *
      CharArray::undef_seg(dest@pre, string_length(dst_str) + 1,
                                     string_length(dst_str) + n@pre + 1) *
      store_string(src@pre, src_str)
  */
  while (dest[i] != 0) {
    i++;
  }

  int j = 0;
  /*@ Inv Assert
      valid_string(dst_str) && valid_string(src_str) &&
      0 <= n@pre && n@pre < INT_MAX &&
      string_length(dst_str) + n@pre + 1 < INT_MAX &&
      i == string_length(dst_str) &&
      0 <= j && j <= n@pre && j <= string_length(src_str) &&
      dest == dest@pre && src == src@pre && n == n@pre &&
      CharArray::full(dest@pre, string_length(dst_str) + j,
                      app(dst_str, sublist(0, j, src_str))) *
      store(dest@pre + (string_length(dst_str) + j) * sizeof(char), char, 0) *
      CharArray::undef_seg(dest@pre, string_length(dst_str) + j + 1,
                                     string_length(dst_str) + n@pre + 1) *
      store_string(src@pre, src_str)
  */
  while (j < n && src[j] != 0) {
    dest[i + j] = src[j];
    j++;
    dest[i + j] = 0;
  }
  return dest;
}
