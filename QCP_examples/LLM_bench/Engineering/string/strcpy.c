#include "string.h"

char *strcpy(char *dest, char *src)
/*@ default */
{
  int i = 0;
  /*@ Inv Assert
      valid_string(src_str) &&
      string_length(src_str) < INT_MAX &&
      0 <= i && i <= string_length(src_str) &&
      dest == dest@pre && src == src@pre &&
      CharArray::full(dest@pre, i, sublist(0, i, src_str)) *
      CharArray::undef_seg(dest@pre, i, string_length(src_str) + 1) *
      store_string(src@pre, src_str)
  */
  while (src[i] != 0) {
    dest[i] = src[i];
    i++;
  }
  dest[i] = 0;
  return dest;
}

char *strncpy(char *dest, char *src, int n)
/*@ default */
{
  int i = 0;
  /*@ Inv Assert
      valid_string(src_str) &&
      0 <= n@pre && n@pre < INT_MAX &&
      0 <= i && i <= n@pre && i <= string_length(src_str) &&
      dest == dest@pre && src == src@pre && n == n@pre &&
      CharArray::full(dest@pre, i, sublist(0, i, src_str)) *
      CharArray::undef_seg(dest@pre, i, n@pre) *
      store_string(src@pre, src_str)
  */
  while (i < n && src[i] != 0) {
    dest[i] = src[i];
    i++;
  }
  /*@ Inv Assert
      exists out,
      valid_string(src_str) &&
      0 <= n@pre && n@pre < INT_MAX &&
      0 <= i && i <= n@pre &&
      strncpy_content(src_str, i, out) &&
      (i < n@pre => string_length(src_str) <= i) &&
      dest == dest@pre && src == src@pre && n == n@pre &&
      CharArray::full(dest@pre, i, out) *
      CharArray::undef_seg(dest@pre, i, n@pre) *
      store_string(src@pre, src_str)
  */
  while (i < n) {
    dest[i] = 0;
    i++;
  }
  return dest;
}
