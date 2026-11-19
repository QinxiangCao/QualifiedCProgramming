/* Object-bounded public contracts. m excludes the terminating zero.
 * capacity bytes are initialized; padding values are existentially hidden.
 * Neither contract grants access beyond the allocated object.
 * QCP's byte-memory proof does not establish ISO C effective-type rules. */
#include "verification_stdlib.h"
#include "verification_list.h"
/*@ Import Coq Require Import SimpleC.EE.stdlib.glibc.strlen_word_lib */
/*@ Import Coq Import StrlenLittleEndian */
/*@ Extern Coq
 (ObjectString::store_string : Z -> Z -> list Z -> Assertion)
 (ObjectString::store_string_exact : Z -> list Z -> Assertion)
*/

unsigned long long strlen_word(const unsigned char *s)
/*@ exact_spec <= capacity_spec
 With m
 Require 0 <= s && s%8 == 0 &&
         s+Zlength(m)+1 <= 18446744073709551615 &&
         8*(Zlength(m)/8+1) <= Zlength(m)+1 &&
         ObjectString::store_string_exact(s,m)
 Ensure __return == Zlength(m) && ObjectString::store_string_exact(s,m)
*/;

unsigned long long strlen_word(const unsigned char *s)
/*@ capacity_spec
 With capacity m
 Require 0 <= s && s%8 == 0 &&
         s+capacity <= 18446744073709551615 &&
         8*(Zlength(m)/8+1) <= capacity &&
         ObjectString::store_string(s,capacity,m)
 Ensure __return == Zlength(m) && ObjectString::store_string(s,capacity,m)
*/;
