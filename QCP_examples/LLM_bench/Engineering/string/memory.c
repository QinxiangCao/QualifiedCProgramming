#include "string.h"

char *memcpy(char *dest, char *src, int n)
/*@ With bytes
    Require all_ascii(bytes) && Zlength(bytes) == n &&
            0 <= n && n < INT_MAX &&
            CharArray::undef_full(dest, n) * CharArray::full(src, n, bytes)
    Ensure __return == dest &&
           CharArray::full(dest, n, bytes) * CharArray::full(src, n, bytes)
*/
{
  int i = 0;
  /*@ Inv Assert
      all_ascii(bytes) && Zlength(bytes) == n@pre &&
      0 <= n@pre && n@pre < INT_MAX &&
      0 <= i && i <= n@pre &&
      dest == dest@pre && src == src@pre && n == n@pre &&
      CharArray::full(dest@pre, i, sublist(0, i, bytes)) *
      CharArray::undef_seg(dest@pre, i, n@pre) *
      CharArray::full(src@pre, n@pre, bytes)
  */
  while (i < n) {
    dest[i] = src[i];
    i++;
  }
  return dest;
}

char *memmove(char *dest, char *src, int n)
/*@ With (bytes memory : list Z) (base source destination mode dest0 src0 n0 : Z)
    Require
      dest == dest0 && src == src0 && n == n0 &&
      0 <= n && n < INT_MAX &&
      ((mode == 0 && all_ascii(bytes) && Zlength(bytes) == n &&
        CharArray::undef_full(dest, n) * CharArray::full(src, n, bytes)) ||
       (mode == 1 && all_ascii(memory) &&
        0 <= source && 0 <= destination &&
        source + n <= Zlength(memory) && destination + n <= Zlength(memory) &&
        src == base + source && dest == base + destination &&
        CharArray::full(base, Zlength(memory), memory)))
    Ensure
      __return == dest0 &&
      ((mode == 0 && CharArray::full(dest0, n0, bytes) * CharArray::full(src0, n0, bytes)) ||
       (mode == 1 && CharArray::full(base, Zlength(memory),
          memmove_content(memory, source, destination, n0))))
*/
{
  if (dest < src) {
    int i = 0;
    /*@ Inv Assert
        dest == dest0 && src == src0 && n == n0 &&
        0 <= n && n < INT_MAX && 0 <= i && i <= n &&
        ((mode == 0 && all_ascii(bytes) && Zlength(bytes) == n &&
          CharArray::full(dest, i, sublist(0, i, bytes)) *
          CharArray::undef_seg(dest, i, n) * CharArray::full(src, n, bytes)) ||
         (mode == 1 && all_ascii(memory) &&
          0 <= destination && destination < source &&
          source + n <= Zlength(memory) && destination + n <= Zlength(memory) &&
          src == base + source && dest == base + destination &&
          CharArray::seg(src, -source, Zlength(memory) - source,
            memmove_content(memory, source, destination, i))))
    */
    while (i < n) {
      int value = src[i];
      /*@ Assert
          dest == dest0 && src == src0 && n == n0 &&
          0 <= n && n < INT_MAX && 0 <= i && i < n &&
          ((mode == 0 && all_ascii(bytes) && Zlength(bytes) == n &&
            value == Znth(i, bytes, 0) &&
            CharArray::full(dest, i, sublist(0, i, bytes)) *
            CharArray::undef_seg(dest, i, n) * CharArray::full(src, n, bytes)) ||
           (mode == 1 && all_ascii(memory) &&
            0 <= destination && destination < source &&
            source + n <= Zlength(memory) && destination + n <= Zlength(memory) &&
            src == base + source && dest == base + destination &&
            value == Znth(source + i, memory, 0) &&
            CharArray::seg(dest, -destination, Zlength(memory) - destination,
              memmove_content(memory, source, destination, i))))
      */
      dest[i] = value;
      i++;
    }
  } else {
    int i = n;
    /*@ Inv Assert
        dest == dest0 && src == src0 && n == n0 &&
        0 <= n && n < INT_MAX && 0 <= i && i <= n &&
        ((mode == 0 && all_ascii(bytes) && Zlength(bytes) == n &&
          CharArray::undef_seg(dest, 0, i) *
          CharArray::full(dest + i * sizeof(char), n - i, sublist(i, n, bytes)) *
          CharArray::full(src, n, bytes)) ||
         (mode == 1 && all_ascii(memory) &&
          0 <= source && source <= destination &&
          source + n <= Zlength(memory) && destination + n <= Zlength(memory) &&
          src == base + source && dest == base + destination &&
          CharArray::seg(src, -source, Zlength(memory) - source,
            memmove_content(memory, source + i, destination + i, n - i))))
    */
    while (i > 0) {
      i--;
      int value = src[i];
      /*@ Assert
          dest == dest0 && src == src0 && n == n0 &&
          0 <= n && n < INT_MAX && 0 <= i && i < n &&
          ((mode == 0 && all_ascii(bytes) && Zlength(bytes) == n &&
            value == Znth(i, bytes, 0) &&
            CharArray::undef_seg(dest, 0, i + 1) *
            CharArray::full(dest + (i + 1) * sizeof(char), n - (i + 1), sublist(i + 1, n, bytes)) *
            CharArray::full(src, n, bytes)) ||
           (mode == 1 && all_ascii(memory) &&
            0 <= source && source <= destination &&
            source + n <= Zlength(memory) && destination + n <= Zlength(memory) &&
            src == base + source && dest == base + destination &&
            value == Znth(source + i, memory, 0) &&
            CharArray::seg(dest, -destination, Zlength(memory) - destination,
              memmove_content(memory, source + (i + 1), destination + (i + 1), n - (i + 1)))))
      */
      dest[i] = value;
    }
  }
  return dest;
}

char *memset(char *s, int c, int n)
/*@ Require 0 <= n && n < INT_MAX &&
            0 <= c && c <= 127 &&
            CharArray::undef_full(s, n)
    Ensure __return == s && CharArray::full(s, n, repeat_Z(c, n))
*/
{
  int i = 0;
  /*@ Inv Assert
      0 <= n@pre && n@pre < INT_MAX &&
      0 <= c@pre && c@pre <= 127 &&
      0 <= i && i <= n@pre &&
      s == s@pre && c == c@pre && n == n@pre &&
      CharArray::full(s@pre, i, repeat_Z(c@pre, i)) *
      CharArray::undef_seg(s@pre, i, n@pre)
  */
  while (i < n) {
    s[i] = c;
    i++;
  }
  return s;
}
