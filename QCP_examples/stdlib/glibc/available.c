#include "available.h"

/* SOURCE ADAPTATION: glibc-2.40/string/strstr.c AVAILABLE, factored into
 * a function. h_l is passed by address to preserve the macro's assignment;
 * the early return preserves || short-circuiting. Arithmetic uses unsigned
 * 64-bit lengths (also on the historical Arch32 QCP memory model). */
int available(const unsigned char *h, probe_size_t *h_l,
              probe_size_t j, probe_size_t n_l)

{
    if (j + n_l <= *h_l)
        return 1;
    *h_l += __strnlen(h + *h_l, n_l + 512)
        /*@ where base = h, bytes = bytes, total = total, offset = known */;
    return j + n_l <= *h_l;
}
