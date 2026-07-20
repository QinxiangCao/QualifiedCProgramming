#include "fme_ge_gmp/gmp/gmp_def.h"

unsigned int gmp_clz(unsigned int x)
/*@
  Require 0 < x && x <= UINT_MAX
  Ensure 0 <= __return && __return < 32 &&
          Z::pow(2, 31) <= x * Z::pow(2, __return) &&
          x * Z::pow(2, __return) < Z::pow(2, 32)
*/
{
  unsigned int c;
  int LOCAL_SHIFT_BITS;

  c = 0;
  LOCAL_SHIFT_BITS = 8;
  if (32 > LOCAL_SHIFT_BITS)
    /*@ Inv Assert
          x == x@pre * Z::pow(2, c) &&
          c % 8 == 0 &&
          0 <= c &&
          c <= 24 &&
          0 < x &&
          x < Z::pow(2, 32) &&
          LOCAL_SHIFT_BITS == 8
    */
    while ((x & (0xffU << (32 - 8))) == 0) {
      c = c + 8;
      x = x << LOCAL_SHIFT_BITS;
    }

  /*@ Assert
        x == x@pre * Z::pow(2, c) &&
        0 <= c &&
        c <= 31 &&
        0 < x &&
        x < Z::pow(2, 32) &&
        LOCAL_SHIFT_BITS == 8
  */
  /*@ Inv Assert
        x == x@pre * Z::pow(2, c) &&
        0 <= c &&
        c <= 31 &&
        0 < x &&
        x < Z::pow(2, 32) &&
        LOCAL_SHIFT_BITS == 8
  */
  while ((x & (1U << (32 - 1))) == 0) {
    c = c + 1;
    x = x << 1;
  }

  return c;
}
