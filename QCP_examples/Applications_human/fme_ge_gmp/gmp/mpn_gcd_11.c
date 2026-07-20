#include "fme_ge_gmp/gmp/gmp_def.h"

unsigned int gmp_clz(unsigned int x)
/*@
  Require 0 < x && x <= UINT_MAX
  Ensure 0 <= __return && __return < 32 &&
          Z::pow(2, 31) <= x * Z::pow(2, __return) &&
          x * Z::pow(2, __return) < Z::pow(2, 32)
*/;

unsigned int gmp_ctz(unsigned int x)
/*@
  Require 0 < x && x <= UINT_MAX
  Ensure exists odd,
          0 <= __return && __return < 32 &&
          odd > 0 && odd % 2 == 1 &&
          x == odd * Z::pow(2, __return)
*/
{
  unsigned int __ctz_x;
  unsigned int __ctz_c;

  __ctz_x = x;
  __ctz_c = gmp_clz(__ctz_x & -__ctz_x);
  return 31 - __ctz_c;
}

unsigned int mpn_gcd_11(unsigned int u, unsigned int v)
/*@
  Require 0 <= u && u <= UINT_MAX &&
          0 <= v && v <= UINT_MAX &&
          u + v > 0
  Ensure __return == Zgcd(u, v)
*/
{
  unsigned int shift;

  if (u == 0)
    return v;
  else if (v == 0)
    return u;

  shift = gmp_ctz(u | v);

  u >>= shift;
  v >>= shift;

  if ( (u & 1) == 0) {
    unsigned int __mp_limb_t_swap__tmp;
    __mp_limb_t_swap__tmp = u;
    u = v;
    v = __mp_limb_t_swap__tmp;
  }

  /*@ Inv Assert
        0 <= shift && shift < 32 &&
        0 <= u@pre && u@pre <= UINT_MAX &&
        0 <= v@pre && v@pre <= UINT_MAX &&
        0 < u && u <= UINT_MAX &&
        0 < v && v <= UINT_MAX &&
        (u & 1) != 0 &&
        Zgcd(u@pre, v@pre) == Z::pow(2, shift) * Zgcd(u, v)
  */
  while ( (v & 1) == 0)
    v >>= 1;

  /*@ Inv Assert
        0 <= shift && shift < 32 &&
        0 <= u@pre && u@pre <= UINT_MAX &&
        0 <= v@pre && v@pre <= UINT_MAX &&
        0 < u && u <= UINT_MAX &&
        0 < v && v <= UINT_MAX &&
        (u & 1) != 0 &&
        (v & 1) != 0 &&
        Zgcd(u@pre, v@pre) == Z::pow(2, shift) * Zgcd(u, v)
  */
  while (u != v)
    {
      if (u > v)
	{
	  u -= v;
	  do
	    u >>= 1;
		  /*@ Inv Assert
		        0 <= shift && shift < 32 &&
		        0 <= u@pre && u@pre <= UINT_MAX &&
		        0 <= v@pre && v@pre <= UINT_MAX &&
		        0 < u && u <= UINT_MAX &&
		        0 < v && v <= UINT_MAX &&
		        (v & 1) != 0 &&
		        Zgcd(u@pre, v@pre) == Z::pow(2, shift) * Zgcd(u, v)
	  */
	  while ( (u & 1) == 0);
	}
      else
	{
	  v -= u;
	  do
	    v >>= 1;
		  /*@ Inv Assert
		        0 <= shift && shift < 32 &&
		        0 <= u@pre && u@pre <= UINT_MAX &&
		        0 <= v@pre && v@pre <= UINT_MAX &&
		        0 < u && u <= UINT_MAX &&
		        0 < v && v <= UINT_MAX &&
		        (u & 1) != 0 &&
		        Zgcd(u@pre, v@pre) == Z::pow(2, shift) * Zgcd(u, v)
	  */
	  while ( (v & 1) == 0);
	}
    }
  return u << shift;
}
