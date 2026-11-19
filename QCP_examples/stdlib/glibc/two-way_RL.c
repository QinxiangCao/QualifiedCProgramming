#include "verification_stdlib.h"
#include "verification_list.h"
/*@ Extern Coq (UCharArray::full : Z -> Z -> list Z -> Assertion)
               (UCharArray::missing_i: Z -> Z -> Z -> Z -> list Z -> Assertion)
               (UCharArray::seg: Z -> Z -> Z -> list Z -> Assertion)
               (UCharArray::undef_full: Z -> Z -> Assertion)
               (UCharArray::undef_seg: Z -> Z -> Z -> Assertion)
               (UCharArray::undef_missing_i: Z -> Z -> Z -> Z -> Assertion)
               (Znth: {A} -> Z -> list A -> A -> A)
               (replace_Znth: {A} -> Z -> A -> list A -> list A)
               (repeat_Z: {A} -> A -> Z -> list A)
*/
#include "int_array_def.h"
#include "safeexecE_two_way_def.h"

/*@ Extern Coq addr := Z */

/*@ Extern Coq (ATrue: {A} -> A -> Prop)
                (maketuple: {A} {B} -> A -> B -> (A * B))
                (applyf: {A} {B} -> (A -> B) -> A -> B)
                (critical_factorization_spec: list Z -> (Z * Z) -> Prop)
                (critical_factorization_prog: list Z -> program unit (Z * Z))
                (first_loop_bind: list Z -> Z -> Z -> Z -> Z -> program unit (Z * Z))
                    (second_loop_bind: list Z -> Z -> Z -> Z -> Z -> Z -> Z -> program unit (Z * Z))
                    (two_way_generic_prog: list Z -> list Z -> program unit (option Z))
                    (two_way_generic_after_factorization: list Z -> list Z -> (Z * Z) -> program unit (option Z))
                    (generic_match_from: list Z -> list Z -> Z -> Z -> Z -> program unit (option Z))
                    (generic_match_from_right: list Z -> list Z -> Z -> Z -> Z -> Z -> program unit (option Z))
                    (generic_match_from_left: list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> program unit (option Z))
                    (generic_match_periodic_from: list Z -> list Z -> Z -> Z -> Z -> Z -> program unit (option Z))
                    (generic_match_periodic_from_right: list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> program unit (option Z))
                    (generic_match_periodic_from_left: list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> program unit (option Z))
                    (valid_skip: list Z -> list Z -> Z -> Z -> Prop)
                    (repetitive_split: list Z -> Z -> Z -> Prop)
                    (periodic_memory_match: list Z -> list Z -> Z -> Z -> Z -> Prop)
                    (matched_range: list Z -> list Z -> Z -> Z -> Z -> Prop)
                    (shift_table_build_prefix: list Z -> Z -> list Z -> Prop)
                    (shift_table_sound: list Z -> list Z -> list Z -> Prop)
                    (uchar_ptr_option_repr: Z -> Z -> Z -> option Z)
                    (match_post: list Z -> list Z -> option Z -> Prop)
                    (memcmp_result: list Z -> Z -> Z -> Z -> Z -> Prop)
                    (match_cond: list Z -> list Z -> Z -> Z -> Prop)
                     */

typedef int size_t;

/* Trusted external primitive. */
int memcmp(const unsigned char *s1, const unsigned char *s2, size_t n)
    /*@ With (base: addr) bytes len off1 off2
        Require s1 == base + off1 * sizeof(unsigned char) &&
                s2 == base + off2 * sizeof(unsigned char) &&
                0 <= off1 && 0 <= off2 && 0 <= n &&
                off1 + n <= len && off2 + n <= len &&
                UCharArray::full(base, len, bytes)
        Ensure memcmp_result(bytes, off1, off2, n, __return) &&
                INT_MIN <= __return && __return <= INT_MAX &&
                UCharArray::full(base, len, bytes)
    */
    ;

/* Switch point for long-needle path. */
/* Compute split position and period. */
static size_t
critical_factorization(const unsigned char *needle, size_t needle_len,
                       size_t *period)
    /*@ bind_spec <= low_level_spec
        With {B} needle0 n0 X (f: (Z * Z) -> program unit B)
        Require safeExec(ATrue, bind(critical_factorization_prog(needle0), f), X) &&
                needle_len == n0 && 0 < needle_len && needle_len <= INT_MAX &&
                UCharArray::full(needle, needle_len, needle0) *
                undef_data_at(period)
        Ensure exists mp,
                safeExec(ATrue, applyf(f, maketuple(__return, mp)), X) &&
                0 < mp && mp <= needle_len &&
                0 <= __return && __return < needle_len &&
                mp + __return <= needle_len &&
                UCharArray::full(needle, needle_len, needle0) *
                data_at(period, size_t, mp)
    */
    /*@ long_needle_bind_spec <= low_level_spec
        With {C} needle0 n0 X (f: (Z * Z) -> program unit C)
        Require safeExec(ATrue, bind(critical_factorization_prog(needle0), f), X) &&
                needle_len == n0 && 0 < needle_len && needle_len <= INT_MAX &&
                UCharArray::full(needle, needle_len, needle0) *
                undef_data_at(period)
        Ensure exists mp,
                safeExec(ATrue, applyf(f, maketuple(__return, mp)), X) &&
                critical_factorization_spec(needle0, maketuple(__return, mp)) &&
                0 < mp && mp <= needle_len &&
                0 <= __return && __return < needle_len &&
                mp + __return <= needle_len &&
                UCharArray::full(needle, needle_len, needle0) *
                data_at(period, size_t, mp)
    */
    ;

static size_t
critical_factorization(const unsigned char *needle, size_t needle_len,
                       size_t *period)
/*@ low_level_spec
    With needle0 n0 X
    Require safeExec(ATrue, critical_factorization_prog(needle0), X) &&
            needle_len == n0 && 0 < needle_len && needle_len <= INT_MAX &&
            UCharArray::full(needle, needle_len, needle0) *
            undef_data_at(period)
    Ensure exists mp,
            safeExec(ATrue, return(maketuple(__return, mp)), X) &&
            0 < mp && mp <= needle_len &&
            0 <= __return && __return < needle_len &&
            mp + __return <= needle_len &&
            UCharArray::full(needle, needle_len, needle0) *
            data_at(period, size_t, mp)
*/
{
    size_t max_suffix, max_suffix_rev;
    size_t j;
    size_t k;
    size_t p;
    unsigned char a, b;
    /* Forward lexicographic pass. */
    max_suffix = ((size_t)-1);
    j = 0;
    p = 1; // MARK: modify
    k = p; // MARK
    /*@ Inv Assert
        safeExec(ATrue, first_loop_bind(needle0, max_suffix, j, k, p),X) &&
        needle_len == n0 &&
        period == period@pre &&
        needle == needle@pre &&
        needle_len == needle_len@pre &&
        0 < needle_len && needle_len <= INT_MAX &&
        0 <= j && j <= needle_len &&
        0 < p && p <= needle_len &&
        0 < k && k <= p &&
        0 <= max_suffix + 1 && max_suffix + 1 <= j &&
        p + max_suffix + 1 <= needle_len &&
        j + k <= needle_len &&
        0 <= max_suffix + k &&
        (max_suffix + k < needle_len) &&

        has_permission(&a) *
        has_permission(&b) *
        has_permission(period) *
        undef_data_at(&max_suffix_rev) *
        UCharArray::full(needle, needle_len, needle0)
    */
    while (j + k < needle_len)
    {
        a = needle[j + k];
        b = needle[max_suffix + k];
        if (a < b)
        {
            j += k;
            k = 1;
            p = j - max_suffix;
        }
        else if (a == b)
        {
            if (k != p)
                ++k;
            else
            {
                j += p; // MARK: modified-original-code
                k = 1;  // MARK: modified-original-code
            }
        }
        else
        {
            max_suffix = j; // MARK: modify for syntax error
            j = j + 1;      // MARK: modify for syntax error
            p = 1;          // MARK: modify
            k = p;
        }
    }
    *period = p;
    /* Reverse lexicographic pass. */
    max_suffix_rev = ((size_t)-1);
    j = 0;
    p = 1; // MARK: modify
    k = p;
    /*@ Inv Assert
        exists mp,
        safeExec(ATrue, second_loop_bind(needle0, max_suffix_rev, j, k, p, max_suffix, mp),X) &&
        needle_len == n0 &&
        period == period@pre &&
        needle == needle@pre &&
        needle_len == needle_len@pre &&
        0 < needle_len && needle_len <= INT_MAX &&
        0 <= j && j <= needle_len &&
        0 < p && p <= needle_len &&
        0 < k && k <= p &&
        0 < mp && mp <= needle_len &&
        0 <= max_suffix + 1 && max_suffix + 1 < needle_len &&
        mp + max_suffix + 1 <= needle_len &&
        0 <= max_suffix_rev + 1 && max_suffix_rev + 1 <= j &&
        p + max_suffix_rev + 1 <= needle_len &&
        j + k <= needle_len &&
        0 <= max_suffix_rev + k && max_suffix_rev + k < needle_len &&

        has_permission(&a) *
        has_permission(&b) *
        data_at(period, size_t, mp) *
        UCharArray::full(needle, needle_len, needle0)
    */
    while (j + k < needle_len)
    {
        a = needle[j + k];
        b = needle[max_suffix_rev + k];
        if (b < a)
        {
            j += k;
            k = 1;
            p = j - max_suffix_rev;
        }
        else if (a == b)
        {
            if (k != p)
                ++k;
            else
            {
                j += p;
                k = 1; // MARK: modified-original-code
            }
        }
        else
        {
            max_suffix_rev = j;
            j = j + 1;
            p = 1; // MARK: modify
            k = p;
        }
    }
    /* Return split index (start of right half). */
    if (max_suffix_rev + 1 < max_suffix + 1)
        return max_suffix + 1;
    *period = p;
    return max_suffix_rev + 1;
}

// LONG_NEEDLE_THRESHOLD 32U
/* Two-Way search: short needle path. */
static inline void *
two_way_short_needle(const unsigned char *haystack, size_t haystack_len,
                     const unsigned char *needle, size_t needle_len)
    /*@ high_level_spec <= low_level_spec
        With hay0 needle0 hn nn
        Require haystack_len == hn && needle_len == nn &&
                0 < needle_len && needle_len <= 32 &&
                0 < haystack_len && haystack_len <= INT_MAX &&
                needle_len <= haystack_len &&
                haystack > 0 && needle > 0 &&
                UCharArray::full(haystack, haystack_len, hay0) *
                UCharArray::full(needle, needle_len, needle0)
    Ensure exists ret,
            match_post(hay0, needle0, ret) &&
            uchar_ptr_option_repr(haystack, __return, sizeof(unsigned char)) == ret &&
            UCharArray::full(haystack, haystack_len, hay0) *
            UCharArray::full(needle, needle_len, needle0)
*/
    ;

static inline void *
two_way_short_needle(const unsigned char *haystack, size_t haystack_len,
                     const unsigned char *needle, size_t needle_len)
/*@ low_level_spec
    With hay0 needle0 hn nn X
    Require haystack_len == hn && needle_len == nn &&
            0 < needle_len && needle_len <= 32 &&
            0 < haystack_len && haystack_len <= INT_MAX &&
            needle_len <= haystack_len &&
            haystack > 0 && needle > 0 &&
            safeExec(ATrue, two_way_generic_prog(hay0, needle0), X) &&
            UCharArray::full(haystack, haystack_len, hay0) *
            UCharArray::full(needle, needle_len, needle0)
    Ensure haystack > 0 && needle > 0 &&
            safeExec(ATrue,
            return(uchar_ptr_option_repr(haystack, __return, sizeof(unsigned char))),
            X) &&
            UCharArray::full(haystack, haystack_len, hay0) *
            UCharArray::full(needle, needle_len, needle0)
*/
{
    size_t i;
    size_t j;
    size_t period;
    size_t suffix;
    /* Precompute split and period. */
    suffix = critical_factorization(needle, needle_len, &period)
        /*@ where (bind_spec) {B = option Z} needle0 = needle0, n0 = needle_len, X = X,
            f = two_way_generic_after_factorization(hay0, needle0) */
        ;
    if (memcmp((needle), (needle + period), (suffix))
        /*@ where base = needle, bytes = needle0_low_level_spec,
                  len = needle_len, off1 = 0, off2 = period, n = suffix */
        == 0)
    {
        /* Periodic case: reuse matched suffix length. */
        size_t memory = 0;
        j = 0;
        /*@ Inv Assert
            exists mp,
                safeExec(ATrue, generic_match_periodic_from(hay0, needle0, suffix, mp, j, memory), X) &&
                needle == needle@pre &&
                haystack == haystack@pre &&
            needle_len == needle_len@pre &&
            haystack_len == haystack_len@pre &&
            haystack@pre > 0 && needle@pre > 0 &&
            0 < needle_len && needle_len <= 32 &&
            0 < haystack_len && haystack_len <= INT_MAX &&

            0 <= j && j <= haystack_len &&
            0 < mp && mp <= needle_len &&
            0 <= suffix && suffix < needle_len &&
            0 <= memory && memory < needle_len &&

            has_permission(&i) *
            data_at(&period, size_t, mp) *
            UCharArray::full(haystack, haystack_len, hay0) *
            UCharArray::full(needle, needle_len, needle0)
        */
        while (((j) <= (haystack_len) - (needle_len))) // Modify : 宏
        {
            const unsigned char *pneedle;
            const unsigned char *phaystack;
            /* Match right half. */
            if (suffix > memory) // MARK: modified-original-code
                i = suffix;
            else
                i = memory;
            pneedle = &needle[i];
            phaystack = &haystack[i + j];
            /*@ Inv Assert
                exists mp,
                    safeExec(ATrue, generic_match_periodic_from_right(hay0, needle0, suffix, mp, j, memory, i), X) &&
                    needle == needle@pre &&
                haystack == haystack@pre &&
                needle_len == needle_len@pre &&
                haystack_len == haystack_len@pre &&
                haystack@pre > 0 && needle@pre > 0 &&
                0 < needle_len && needle_len <= 32 &&
                0 < haystack_len && haystack_len <= INT_MAX &&

                0 <= j && j <= haystack_len - needle_len &&
                0 < mp  && mp <= needle_len &&
                0 <= suffix && suffix < needle_len &&
                0 <= memory && memory < needle_len &&
                suffix <= i && memory <= i && i <= needle_len &&

                data_at(&period, size_t, mp) *
                data_at(&pneedle, unsigned char *, needle + i * sizeof(unsigned char)) *
                data_at(&phaystack, unsigned char *, haystack + (i + j) * sizeof(unsigned char)) *
                UCharArray::full(haystack, haystack_len, hay0) *
                UCharArray::full(needle, needle_len, needle0)
            */
            while (i < needle_len) // 右侧匹配 // MARK: modified-original-code
            {
                if (*pneedle != *phaystack)
                    break;
                pneedle = pneedle + 1;
                phaystack = phaystack + 1;
                i = i + 1;
            }
            if (needle_len <= i)
            {
                /* Match left half. */
                i = suffix - 1;
                pneedle = &needle[i];
                phaystack = &haystack[i + j];
                /*@ Inv Assert
                        exists mp,
                        safeExec(ATrue, generic_match_periodic_from_left(hay0, needle0, suffix, mp, j, memory, i), X) &&
                        needle == needle@pre &&
                    haystack == haystack@pre &&
                    needle_len == needle_len@pre &&
                    haystack_len == haystack_len@pre &&
                    haystack@pre > 0 && needle@pre > 0 &&
                    0 < needle_len && needle_len <= 32 &&
                    0 < haystack_len && haystack_len <= INT_MAX &&

                    0 <= j && j <= haystack_len - needle_len &&
                    0 < mp  && mp <= needle_len &&
                    0 <= suffix && suffix < needle_len &&
                    0 <= memory && memory < needle_len &&
                    0 <= i + 1 && i + 1 <= suffix &&

                    data_at(&period, size_t, mp) *
                    data_at(&pneedle, unsigned char *, needle + i * sizeof(unsigned char)) *
                    data_at(&phaystack, unsigned char *, haystack + (i + j) * sizeof(unsigned char)) *
                    UCharArray::full(haystack, haystack_len, hay0) *
                    UCharArray::full(needle, needle_len, needle0)
                */
                while (memory < i + 1) // MARK: modified-original-code
                {
                    if (*pneedle != *phaystack)
                        break;
                    pneedle = pneedle - 1;
                    phaystack = phaystack - 1;
                    i = i - 1;
                }
                if (i + 1 < memory + 1)
                    return (void *)(haystack + j);
                j += period;
                memory = needle_len - period;
            }
            else
            {
                j += i - suffix + 1;
                memory = 0;
            }
        }
    }
    else
    {
        const unsigned char *phaystack;
        /* Distinct-halves case: quick reject at needle[suffix]. */
        unsigned char needle_suffix = needle[suffix];
        if (suffix > needle_len - suffix) // MARK: ternary-to-if
            period = suffix + 1;          // MARK: ternary-to-if
        else
            period = needle_len - suffix + 1; // MARK: ternary-to-if
        j = 0;
        /*@ Inv Assert
                exists mp,
                safeExec(ATrue, generic_match_from(hay0, needle0, suffix, mp, j), X) &&
                needle == needle@pre &&
            haystack == haystack@pre &&
            needle_len == needle_len@pre &&
            haystack_len == haystack_len@pre &&
            haystack@pre > 0 && needle@pre > 0 &&
            0 < needle_len && needle_len <= 32 &&
            0 < haystack_len && haystack_len <= INT_MAX &&
            needle_len <= haystack_len &&

            0 <= j &&
            0 < mp && mp <= needle_len &&
            0 <= suffix && suffix < needle_len &&

            has_permission(&i) *
            has_permission(&phaystack) *
            data_at(&period, size_t, mp) *
            data_at(&needle_suffix, unsigned char, needle0[suffix]) *
            UCharArray::full(haystack, haystack_len, hay0) *
            UCharArray::full(needle, needle_len, needle0)
        */
        while (((j) <= (haystack_len) - (needle_len)))
        {
            unsigned char haystack_char;
            const unsigned char *pneedle;
            phaystack = &haystack[suffix + j];
            haystack_char = *phaystack;
            phaystack = phaystack + 1;
            /*@ Inv Assert
                    exists mp phay_ch,
                    safeExec(ATrue, generic_match_from(hay0, needle0, suffix, mp, j), X) &&
                    needle == needle@pre &&
                haystack == haystack@pre &&
                needle_len == needle_len@pre &&
                haystack_len == haystack_len@pre &&
                haystack@pre > 0 && needle@pre > 0 &&
                0 < needle_len && needle_len <= 32 &&
                0 < haystack_len && haystack_len <= INT_MAX &&

                0 <= j && j <= haystack_len - needle_len &&
                0 < mp && mp <= needle_len &&
                0 <= suffix && suffix < needle_len &&
                0 <= suffix + j + 1 &&
                suffix + j + 1 <= haystack_len &&
                phay_ch == Znth(suffix + j, hay0, 0) &&

                has_permission(&i) *
                has_permission(&pneedle) *
                data_at(&period, size_t, mp) *
                data_at(&needle_suffix, unsigned char, needle0[suffix]) *
                data_at(&phaystack, unsigned char *, haystack + (suffix + j + 1) * sizeof(unsigned char)) *
                data_at(&haystack_char, unsigned char, phay_ch) *
                UCharArray::full(haystack, haystack_len, hay0) *
                UCharArray::full(needle, needle_len, needle0)
            */
            while (needle_suffix != haystack_char)
            {
                j = j + 1;
                if (!((j) <= (haystack_len) - (needle_len)))
                    return ((void *)0); // MARK: modify goto; 等价于 NULL
                haystack_char = *phaystack;
                phaystack = phaystack + 1;
            }

            /* Match right half. */
            i = suffix + 1;
            pneedle = &needle[i];
            phaystack = &haystack[i + j];
            /*@ Inv Assert
                    exists mp phay_ch,
                    safeExec(ATrue, generic_match_from_right(hay0, needle0, suffix, mp, j, i), X) &&
                    needle == needle@pre &&
                haystack == haystack@pre &&
                needle_len == needle_len@pre &&
                haystack_len == haystack_len@pre &&
                haystack@pre > 0 && needle@pre > 0 &&
                0 < needle_len && needle_len <= 32 &&
                0 < haystack_len && haystack_len <= INT_MAX &&

                0 < mp && mp <= needle_len &&
                0 <= suffix && suffix < needle_len &&
                0 <= suffix + 1 && suffix + 1 <= i && i <= needle_len &&
                0 <= j && j <= haystack_len - needle_len &&
                0 <= suffix + j + 1 && suffix + j + 1 <= i + j &&
                suffix + j + 1 <= suffix + 1 + j &&
                0 <= suffix + 1 + j &&
                0 <= i + j && i + j <= haystack_len &&
                suffix + 1 + j <= haystack_len &&

                data_at(&period, size_t, mp) *
                data_at(&needle_suffix, unsigned char, needle0[suffix]) *
                data_at(&pneedle, unsigned char *, needle + i * sizeof(unsigned char)) *
                data_at(&phaystack, unsigned char *, haystack + (i + j) * sizeof(unsigned char)) *
                data_at(&haystack_char, unsigned char, phay_ch) *
                UCharArray::full(haystack, haystack_len, hay0) *
                UCharArray::full(needle, needle_len, needle0)
            */
            while (i < needle_len)
            {
                haystack_char = *phaystack;
                if (*pneedle != haystack_char)
                    break;
                pneedle = pneedle + 1;
                phaystack = phaystack + 1;
                i = i + 1;
            }
            if (needle_len <= i)
            {
                /* Match left half. */
                i = suffix - 1;
                pneedle = &needle[i];
                phaystack = &haystack[i + j];
                /*@ Inv Assert
                        exists mp phay_ch,
                        safeExec(ATrue, generic_match_from_left(hay0, needle0, suffix, mp, j, 0, i), X) &&
                        needle == needle@pre &&
                    haystack == haystack@pre &&
                    needle_len == needle_len@pre &&
                    haystack_len == haystack_len@pre &&
                    haystack@pre > 0 && needle@pre > 0 &&
                    0 < needle_len && needle_len <= 32 &&
                    0 < haystack_len && haystack_len <= INT_MAX &&

                    0 < mp && mp <= needle_len &&
                    0 <= suffix && suffix < needle_len &&
                    0 <= j && j <= haystack_len - needle_len &&
                    0 <= i + 1 && i + 1 <= suffix + 1 &&
                    0 <= i + 1 + j && i + 1 + j <= haystack_len &&

                    data_at(&period, size_t, mp) *
                    data_at(&needle_suffix, unsigned char, needle0[suffix]) *
                    data_at(&pneedle, unsigned char *, needle + i * sizeof(unsigned char)) *
                    data_at(&phaystack, unsigned char *, haystack + (i + j) * sizeof(unsigned char)) *
                    data_at(&haystack_char, unsigned char, phay_ch) *
                    UCharArray::full(haystack, haystack_len, hay0) *
                    UCharArray::full(needle, needle_len, needle0)
                */
                while (i != ((size_t)-1)) // MARK: modified-original-code
                {
                    haystack_char = *phaystack;
                    if (*pneedle != haystack_char)
                        break;
                    pneedle = pneedle - 1;
                    phaystack = phaystack - 1;
                    i = i - 1;
                }
                if (i == ((size_t)-1))
                    return (void *)(haystack + j);
                j += period;
            }
            else
                j += i - suffix + 1;
        }
    }
    return ((void *)0); // MARK: modify goto; equivalent to ret0
}

/* Two-Way search: long needle path with shift table. */
static void *
two_way_long_needle(const unsigned char *haystack, size_t haystack_len,
                    const unsigned char *needle, size_t needle_len)
    /*@ high_level_spec <= low_level_spec
        With hay0 needle0 hn nn
        Require haystack_len == hn && needle_len == nn &&
                32 < needle_len && needle_len <= haystack_len &&
                haystack_len <= INT_MAX &&
                haystack > 0 && needle > 0 &&
                UCharArray::full(haystack, haystack_len, hay0) *
                UCharArray::full(needle, needle_len, needle0)
        Ensure exists ret,
                match_post(hay0, needle0, ret) &&
                uchar_ptr_option_repr(haystack, __return, sizeof(unsigned char)) == ret &&
                UCharArray::full(haystack, haystack_len, hay0) *
                UCharArray::full(needle, needle_len, needle0)
    */
    ;

static void *
two_way_long_needle(const unsigned char *haystack, size_t haystack_len,
                    const unsigned char *needle, size_t needle_len)
/*@ low_level_spec
    With hay0 needle0 hn nn X
    Require haystack_len == hn && needle_len == nn &&
            32 < needle_len && needle_len <= haystack_len &&
            haystack_len <= INT_MAX &&
            haystack > 0 && needle > 0 &&
            safeExec(ATrue, two_way_generic_prog(hay0, needle0), X) &&
            UCharArray::full(haystack, haystack_len, hay0) *
            UCharArray::full(needle, needle_len, needle0)
    Ensure haystack > 0 && needle > 0 &&
            safeExec(ATrue,
            return(uchar_ptr_option_repr(haystack, __return, sizeof(unsigned char))),
            X) &&
            UCharArray::full(haystack, haystack_len, hay0) *
            UCharArray::full(needle, needle_len, needle0)
*/
{
    size_t i;
    size_t j;
    size_t period;
    size_t suffix;
    int shift_table[1U << 8];
    /* Precompute split and period. */
    suffix = critical_factorization(needle, needle_len, &period)
        /*@ where (long_needle_bind_spec) {C = option Z} needle0 = needle0, n0 = needle_len, X = X,
            f = two_way_generic_after_factorization(hay0, needle0) */
        ;
    /* Build bad-character shifts. */
    /*@ Inv Assert
        exists mp,
        safeExec(ATrue,
            applyf(two_way_generic_after_factorization(hay0, needle0),
                   maketuple(suffix, mp)), X) &&
        critical_factorization_spec(needle0, maketuple(suffix, mp)) &&
        haystack == haystack@pre &&
        needle == needle@pre &&
        haystack_len == haystack_len@pre &&
        needle_len == needle_len@pre &&
        32 < needle_len && needle_len <= haystack_len &&
        haystack_len <= INT_MAX &&
        haystack > 0 && needle > 0 &&
        0 <= i && i <= 256 &&
        0 < mp && mp <= needle_len &&
        0 <= suffix && suffix < needle_len &&
        mp + suffix <= needle_len &&

        has_permission(&j) *
        data_at(&period, size_t, mp) *
        IntArray::seg(shift_table, 0, i, repeat_Z(needle_len, i)) *
        IntArray::undef_seg(shift_table, i, 256) *
        UCharArray::full(haystack, haystack_len, hay0) *
        UCharArray::full(needle, needle_len, needle0)
    */
    for (i = 0; i < 1U << 8; i++) // 后字符检查，shift_table
        shift_table[i] = needle_len;
    /*@ Assert
        exists mp table,
        safeExec(ATrue,
            applyf(two_way_generic_after_factorization(hay0, needle0),
                   maketuple(suffix, mp)), X) &&
        critical_factorization_spec(needle0, maketuple(suffix, mp)) &&
        shift_table_build_prefix(needle0, 0, table) &&
        haystack == haystack@pre &&
        needle == needle@pre &&
        haystack_len == haystack_len@pre &&
        needle_len == needle_len@pre &&
        32 < needle_len && needle_len <= haystack_len &&
        haystack_len <= INT_MAX &&
        haystack > 0 && needle > 0 &&
        0 < mp && mp <= needle_len &&
        0 <= suffix && suffix < needle_len &&
        mp + suffix <= needle_len &&

        has_permission(&j) *
        has_permission(&i) *
        data_at(&period, size_t, mp) *
        IntArray::full(shift_table, 256, table) *
        UCharArray::full(haystack, haystack_len, hay0) *
        UCharArray::full(needle, needle_len, needle0)
    */
    /*@ Inv Assert
        exists mp table,
        safeExec(ATrue,
            applyf(two_way_generic_after_factorization(hay0, needle0),
                   maketuple(suffix, mp)), X) &&
        critical_factorization_spec(needle0, maketuple(suffix, mp)) &&
        shift_table_build_prefix(needle0, i, table) &&
        haystack == haystack@pre &&
        needle == needle@pre &&
        haystack_len == haystack_len@pre &&
        needle_len == needle_len@pre &&
        32 < needle_len && needle_len <= haystack_len &&
        haystack_len <= INT_MAX &&
        haystack > 0 && needle > 0 &&
        0 <= i && i <= needle_len &&
        0 <= Znth(i, needle0, 0) && Znth(i, needle0, 0) < 256 &&
        0 < mp && mp <= needle_len &&
        0 <= suffix && suffix < needle_len &&
        mp + suffix <= needle_len &&

        has_permission(&j) *
        data_at(&period, size_t, mp) *
        IntArray::full(shift_table, 256, table) *
        UCharArray::full(haystack, haystack_len, hay0) *
        UCharArray::full(needle, needle_len, needle0)
    */
    for (i = 0; i < needle_len; i++)
    {
        /*@ Assert
            exists mp table,
            safeExec(ATrue,
                applyf(two_way_generic_after_factorization(hay0, needle0),
                       maketuple(suffix, mp)), X) &&
            critical_factorization_spec(needle0, maketuple(suffix, mp)) &&
            shift_table_build_prefix(needle0, i, table) &&
            haystack == haystack@pre &&
            needle == needle@pre &&
            haystack_len == haystack_len@pre &&
            needle_len == needle_len@pre &&
            32 < needle_len && needle_len <= haystack_len &&
            haystack_len <= INT_MAX &&
            haystack > 0 && needle > 0 &&
            0 <= i && i < needle_len &&
            0 <= Znth(i, needle0, 0) && Znth(i, needle0, 0) < 256 &&
            0 < mp && mp <= needle_len &&
            0 <= suffix && suffix < needle_len &&
            mp + suffix <= needle_len &&

            has_permission(&j) *
            data_at(&period, size_t, mp) *
            IntArray::full(shift_table, 256, table) *
            UCharArray::full(haystack, haystack_len, hay0) *
            UCharArray::missing_i(needle, i, 0, needle_len, needle0) *
            data_at(needle + i * sizeof(unsigned char), unsigned char, Znth(i, needle0, 0))
        */
        shift_table[needle[i]] = needle_len - i - 1;
    }
    /*@ Assert
        exists mp table,
        safeExec(ATrue,
            applyf(two_way_generic_after_factorization(hay0, needle0),
                   maketuple(suffix, mp)), X) &&
        critical_factorization_spec(needle0, maketuple(suffix, mp)) &&
        shift_table_sound(hay0, needle0, table) &&
        haystack == haystack@pre &&
        needle == needle@pre &&
        haystack_len == haystack_len@pre &&
        needle_len == needle_len@pre &&
        32 < needle_len && needle_len <= haystack_len &&
        haystack_len <= INT_MAX &&
        haystack > 0 && needle > 0 &&
        0 < mp && mp <= needle_len &&
        0 <= suffix && suffix < needle_len &&
        mp + suffix <= needle_len &&

        has_permission(&j) *
        has_permission(&i) *
        data_at(&period, size_t, mp) *
        IntArray::full(shift_table, 256, table) *
        UCharArray::full(haystack, haystack_len, hay0) *
        UCharArray::full(needle, needle_len, needle0)
    */
    /* Compare right half first. */
    if (memcmp((needle), (needle + period), (suffix))
        /*@ where base = needle, bytes = needle0_low_level_spec,
                  len = needle_len, off1 = 0, off2 = period, n = suffix */
        == 0)
    {
        /* Periodic case: reuse matched suffix length. */
        /* restored original control-flow: no pre-loop j shift */ // MARK: modified-original-code
        size_t memory = 0;
        size_t shift;
        j = 0;
        /*@ Inv Assert
            exists mp table,
            safeExec(ATrue, generic_match_periodic_from(hay0, needle0, suffix, mp, j, memory), X) &&
            critical_factorization_spec(needle0, maketuple(suffix, mp)) &&
            repetitive_split(needle0, suffix, mp) &&
            periodic_memory_match(hay0, needle0, j, mp, memory) &&
            shift_table_sound(hay0, needle0, table) &&
            haystack == haystack@pre &&
            needle == needle@pre &&
            haystack_len == haystack_len@pre &&
            needle_len == needle_len@pre &&
            haystack@pre > 0 && needle@pre > 0 &&
            32 < needle_len && needle_len <= haystack_len &&
            haystack_len <= INT_MAX &&

            0 <= j && j <= haystack_len &&
            0 < mp && mp <= needle_len &&
            0 <= suffix && suffix < needle_len &&
            0 <= memory && memory < needle_len &&

            has_permission(&i) *
            has_permission(&shift) *
            data_at(&period, size_t, mp) *
            IntArray::full(shift_table, 256, table) *
            UCharArray::full(haystack, haystack_len, hay0) *
            UCharArray::full(needle, needle_len, needle0)
        */
        while ((j) <= (haystack_len) - (needle_len))
        {
            const unsigned char *pneedle;
            const unsigned char *phaystack;
            /* Last-byte filter from shift table. */
            /*@ Assert
                exists mp table,
                safeExec(ATrue, generic_match_periodic_from(hay0, needle0, suffix, mp, j, memory), X) &&
                critical_factorization_spec(needle0, maketuple(suffix, mp)) &&
                repetitive_split(needle0, suffix, mp) &&
                periodic_memory_match(hay0, needle0, j, mp, memory) &&
                shift_table_sound(hay0, needle0, table) &&
                haystack == haystack@pre &&
                needle == needle@pre &&
                haystack_len == haystack_len@pre &&
                needle_len == needle_len@pre &&
                haystack@pre > 0 && needle@pre > 0 &&
                32 < needle_len && needle_len <= haystack_len &&
                haystack_len <= INT_MAX &&

                0 <= j && j <= haystack_len - needle_len &&
                0 <= j + needle_len - 1 && j + needle_len - 1 < haystack_len &&
                0 <= Znth(j + needle_len - 1, hay0, 0) &&
                Znth(j + needle_len - 1, hay0, 0) < 256 &&
                0 < mp && mp <= needle_len &&
                0 <= suffix && suffix < needle_len &&
                0 <= memory && memory < needle_len &&

                has_permission(&pneedle) *
                has_permission(&phaystack) *
                has_permission(&i) *
                undef_data_at(&shift, size_t) *
                data_at(&period, size_t, mp) *
                IntArray::full(shift_table, 256, table) *
                UCharArray::missing_i(haystack, j + needle_len - 1, 0, haystack_len, hay0) *
                data_at(haystack + (j + needle_len - 1) * sizeof(unsigned char),
                        unsigned char, Znth(j + needle_len - 1, hay0, 0)) *
                UCharArray::full(needle, needle_len, needle0)
            */
            shift = shift_table[haystack[j + needle_len - 1]];
            if (0 < shift)
            {
                if (memory && shift < period)
                {
                    shift = needle_len - period;
                }
                /*@ Assert
                    exists mp table,
                    safeExec(ATrue, generic_match_periodic_from(hay0, needle0, suffix, mp, j, memory), X) &&
                    critical_factorization_spec(needle0, maketuple(suffix, mp)) &&
                    repetitive_split(needle0, suffix, mp) &&
                    periodic_memory_match(hay0, needle0, j, mp, memory) &&
                    valid_skip(hay0, needle0, j, shift) &&
                    shift_table_sound(hay0, needle0, table) &&
                    haystack == haystack@pre &&
                    needle == needle@pre &&
                    haystack_len == haystack_len@pre &&
                    needle_len == needle_len@pre &&
                    haystack@pre > 0 && needle@pre > 0 &&
                    32 < needle_len && needle_len <= haystack_len &&
                    haystack_len <= INT_MAX &&
                    0 <= j && j <= haystack_len - needle_len &&
                    0 < shift &&
                    0 < mp && mp <= needle_len &&
                    0 <= suffix && suffix < needle_len &&

                    has_permission(&pneedle) *
                    has_permission(&phaystack) *
                    has_permission(&i) *
                    data_at(&period, size_t, mp) *
                    IntArray::full(shift_table, 256, table) *
                    UCharArray::full(haystack, haystack_len, hay0) *
                    UCharArray::full(needle, needle_len, needle0)
                */
                memory = 0;
                j += shift;
                continue; // 使得最后一个字符对齐才会进入two_way的流程
            }
            /*@ Assert
                exists mp table,
                safeExec(ATrue, generic_match_periodic_from(hay0, needle0, suffix, mp, j, memory), X) &&
                critical_factorization_spec(needle0, maketuple(suffix, mp)) &&
                repetitive_split(needle0, suffix, mp) &&
                periodic_memory_match(hay0, needle0, j, mp, memory) &&
                shift == 0 &&
                match_cond(hay0, needle0, j, needle_len - 1) &&
                shift_table_sound(hay0, needle0, table) &&
                haystack == haystack@pre &&
                needle == needle@pre &&
                haystack_len == haystack_len@pre &&
                needle_len == needle_len@pre &&
                haystack@pre > 0 && needle@pre > 0 &&
                32 < needle_len && needle_len <= haystack_len &&
                haystack_len <= INT_MAX &&
                0 <= j && j <= haystack_len - needle_len &&
                0 < mp && mp <= needle_len &&
                0 <= suffix && suffix < needle_len &&
                0 <= memory && memory < needle_len &&

                has_permission(&pneedle) *
                has_permission(&phaystack) *
                has_permission(&i) *
                data_at(&period, size_t, mp) *
                IntArray::full(shift_table, 256, table) *
                UCharArray::full(haystack, haystack_len, hay0) *
                UCharArray::full(needle, needle_len, needle0)
            */
            /* Match right half (last byte already matched). */
            if (suffix > memory) // MARK: ternary-to-if
                i = suffix;      // MARK: ternary-to-if
            else
                i = memory; // MARK: ternary-to-if
            pneedle = &needle[i];
            phaystack = &haystack[i + j];
            /*@ Inv Assert
                exists mp table,
                safeExec(ATrue, generic_match_periodic_from_right(hay0, needle0, suffix, mp, j, memory, i), X) &&
                critical_factorization_spec(needle0, maketuple(suffix, mp)) &&
                repetitive_split(needle0, suffix, mp) &&
                periodic_memory_match(hay0, needle0, j, mp, memory) &&
                matched_range(hay0, needle0, j, suffix, i) &&
                match_cond(hay0, needle0, j, needle_len - 1) &&
                shift_table_sound(hay0, needle0, table) &&
                needle == needle@pre &&
                haystack == haystack@pre &&
                needle_len == needle_len@pre &&
                haystack_len == haystack_len@pre &&
                haystack@pre > 0 && needle@pre > 0 &&
                32 < needle_len && needle_len <= haystack_len &&
                haystack_len <= INT_MAX &&

                0 <= j && j <= haystack_len - needle_len &&
                0 < mp && mp <= needle_len &&
                0 <= suffix && suffix < needle_len &&
                0 <= memory && memory < needle_len &&
                suffix <= i && memory <= i && i <= needle_len - 1 &&

                has_permission(&shift) *
                data_at(&period, size_t, mp) *
                data_at(&pneedle, unsigned char *, needle + i * sizeof(unsigned char)) *
                data_at(&phaystack, unsigned char *, haystack + (i + j) * sizeof(unsigned char)) *
                IntArray::full(shift_table, 256, table) *
                UCharArray::full(haystack, haystack_len, hay0) *
                UCharArray::full(needle, needle_len, needle0)
            */
            while (i < needle_len - 1) // 右侧匹配 // MARK: modified-original-code
            {
                if (*pneedle != *phaystack)
                    break;
                pneedle = pneedle + 1;
                phaystack = phaystack + 1;
                i = i + 1;
            }
            if (needle_len - 1 <= i)
            {
                /* Match left half. */
                i = suffix - 1;
                pneedle = &needle[i];
                phaystack = &haystack[i + j];
                /*@ Inv Assert
                    exists mp table,
                    safeExec(ATrue, generic_match_periodic_from_left(hay0, needle0, suffix, mp, j, memory, i), X) &&
                    critical_factorization_spec(needle0, maketuple(suffix, mp)) &&
                    repetitive_split(needle0, suffix, mp) &&
                    periodic_memory_match(hay0, needle0, j, mp, memory) &&
                    matched_range(hay0, needle0, j, i + 1, needle_len) &&
                    shift_table_sound(hay0, needle0, table) &&
                    needle == needle@pre &&
                    haystack == haystack@pre &&
                    needle_len == needle_len@pre &&
                    haystack_len == haystack_len@pre &&
                    haystack@pre > 0 && needle@pre > 0 &&
                    32 < needle_len && needle_len <= haystack_len &&
                    haystack_len <= INT_MAX &&

                    0 <= j && j <= haystack_len - needle_len &&
                    0 < mp && mp <= needle_len &&
                    0 <= suffix && suffix < needle_len &&
                    0 <= memory && memory < needle_len &&
                    0 <= i + 1 && i + 1 <= suffix &&

                    has_permission(&shift) *
                    data_at(&period, size_t, mp) *
                    data_at(&pneedle, unsigned char *, needle + i * sizeof(unsigned char)) *
                    data_at(&phaystack, unsigned char *, haystack + (i + j) * sizeof(unsigned char)) *
                    IntArray::full(shift_table, 256, table) *
                    UCharArray::full(haystack, haystack_len, hay0) *
                    UCharArray::full(needle, needle_len, needle0)
                */
                while (memory < i + 1) // MARK: modified-original-code
                {
                    if (*pneedle != *phaystack)
                        break;
                    pneedle = pneedle - 1;
                    phaystack = phaystack - 1;
                    i = i - 1;
                }
                if (i + 1 < memory + 1)
                    /*@ Assert
                        exists mp table,
                        safeExec(ATrue, generic_match_periodic_from_left(hay0, needle0, suffix, mp, j, memory, i), X) &&
                        critical_factorization_spec(needle0, maketuple(suffix, mp)) &&
                        repetitive_split(needle0, suffix, mp) &&
                        periodic_memory_match(hay0, needle0, j, mp, memory) &&
                        matched_range(hay0, needle0, j, i + 1, needle_len) &&
                        shift_table_sound(hay0, needle0, table) &&
                        haystack == haystack@pre &&
                        needle == needle@pre &&
                        haystack_len == haystack_len@pre &&
                        needle_len == needle_len@pre &&
                        haystack@pre > 0 && needle@pre > 0 &&
                        32 < needle_len && needle_len <= haystack_len &&
                        haystack_len <= INT_MAX &&

                        0 <= j && j <= haystack_len - needle_len &&
                        0 < mp && mp <= needle_len &&
                        0 <= suffix && suffix < needle_len &&
                        0 <= memory && memory < needle_len &&
                        0 <= i + 1 && i + 1 <= suffix &&
                        i + 1 < memory + 1 &&

                        has_permission(&pneedle) *
                        has_permission(&phaystack) *
                        has_permission(&shift) *
                        data_at(&period, size_t, mp) *
                        IntArray::undef_full(shift_table, 256) *
                        UCharArray::full(haystack, haystack_len, hay0) *
                        UCharArray::full(needle, needle_len, needle0)
                    */
                    return (void *)(haystack + j);
                j += period;
                memory = needle_len - period;
            }
            else
            {
                j += i - suffix + 1;
                memory = 0;
            }
        }
    }
    else
    {
        /* Distinct-halves case. */
        size_t shift;
        if (suffix > needle_len - suffix) // MARK: ternary-to-if
            period = suffix + 1;          // MARK: ternary-to-if
        else
            period = needle_len - suffix + 1; // MARK: ternary-to-if
        j = 0;
        /*@ Inv Assert
            exists table,
            safeExec(ATrue, generic_match_from(hay0, needle0, suffix, period, j), X) &&
            shift_table_sound(hay0, needle0, table) &&
            haystack == haystack@pre &&
            needle == needle@pre &&
            haystack_len == haystack_len@pre &&
            needle_len == needle_len@pre &&
            haystack@pre > 0 && needle@pre > 0 &&
            32 < needle_len && needle_len <= haystack_len &&
            haystack_len <= INT_MAX &&

            0 <= j && j <= haystack_len &&
            0 < suffix && 0 <= suffix && suffix < needle_len &&
            0 < period && period <= needle_len &&

            has_permission(&i) *
            has_permission(&shift) *
            IntArray::full(shift_table, 256, table) *
            UCharArray::full(haystack, haystack_len, hay0) *
            UCharArray::full(needle, needle_len, needle0)
        */
        while ((j) <= (haystack_len) - (needle_len))
        {
            const unsigned char *pneedle;
            const unsigned char *phaystack;
            /* Last-byte filter from shift table. */
            /*@ Assert
                exists table,
                safeExec(ATrue, generic_match_from(hay0, needle0, suffix, period, j), X) &&
                shift_table_sound(hay0, needle0, table) &&
                haystack == haystack@pre &&
                needle == needle@pre &&
                haystack_len == haystack_len@pre &&
                needle_len == needle_len@pre &&
                haystack@pre > 0 && needle@pre > 0 &&
                32 < needle_len && needle_len <= haystack_len &&
                haystack_len <= INT_MAX &&

                0 <= j && j <= haystack_len - needle_len &&
                0 <= j + needle_len - 1 && j + needle_len - 1 < haystack_len &&
                0 <= Znth(j + needle_len - 1, hay0, 0) &&
                Znth(j + needle_len - 1, hay0, 0) < 256 &&
                0 < suffix && 0 <= suffix && suffix < needle_len &&
                0 < period && period <= needle_len &&

                has_permission(&pneedle) *
                has_permission(&phaystack) *
                has_permission(&i) *
                undef_data_at(&shift, size_t) *
                IntArray::full(shift_table, 256, table) *
                UCharArray::missing_i(haystack, j + needle_len - 1, 0, haystack_len, hay0) *
                data_at(haystack + (j + needle_len - 1) * sizeof(unsigned char),
                        unsigned char, Znth(j + needle_len - 1, hay0, 0)) *
                UCharArray::full(needle, needle_len, needle0)
            */
            shift = shift_table[haystack[j + needle_len - 1]];
            if (0 < shift)
            {
                /*@ Assert
                    exists table,
                    safeExec(ATrue, generic_match_from(hay0, needle0, suffix, period, j), X) &&
                    valid_skip(hay0, needle0, j, shift) &&
                    shift_table_sound(hay0, needle0, table) &&
                    haystack == haystack@pre &&
                    needle == needle@pre &&
                    haystack_len == haystack_len@pre &&
                    needle_len == needle_len@pre &&
                    haystack@pre > 0 && needle@pre > 0 &&
                    32 < needle_len && needle_len <= haystack_len &&
                    haystack_len <= INT_MAX &&
                    0 <= j && j <= haystack_len - needle_len &&
                    0 < shift &&
                    0 < suffix && 0 <= suffix && suffix < needle_len &&
                    0 < period && period <= needle_len &&

                    has_permission(&pneedle) *
                    has_permission(&phaystack) *
                    has_permission(&i) *
                    IntArray::full(shift_table, 256, table) *
                    UCharArray::full(haystack, haystack_len, hay0) *
                    UCharArray::full(needle, needle_len, needle0)
                */
                j += shift;
                continue; // 非周期也是一样的，利用了坏字符规则优先对齐最后一个字符，再进入two_way的流程
            }
            /*@ Assert
                exists table,
                safeExec(ATrue, generic_match_from(hay0, needle0, suffix, period, j), X) &&
                shift == 0 &&
                match_cond(hay0, needle0, j, needle_len - 1) &&
                shift_table_sound(hay0, needle0, table) &&
                haystack == haystack@pre &&
                needle == needle@pre &&
                haystack_len == haystack_len@pre &&
                needle_len == needle_len@pre &&
                haystack@pre > 0 && needle@pre > 0 &&
                32 < needle_len && needle_len <= haystack_len &&
                haystack_len <= INT_MAX &&
                0 <= j && j <= haystack_len - needle_len &&
                0 < suffix && 0 <= suffix && suffix < needle_len &&
                0 < period && period <= needle_len &&

                has_permission(&pneedle) *
                has_permission(&phaystack) *
                has_permission(&i) *
                IntArray::full(shift_table, 256, table) *
                UCharArray::full(haystack, haystack_len, hay0) *
                UCharArray::full(needle, needle_len, needle0)
            */
            /* Match right half (last byte already matched). */
            i = suffix;
            pneedle = &needle[i];
            phaystack = &haystack[i + j];
            /*@ Inv Assert
                exists table,
                    safeExec(ATrue, generic_match_from_right(hay0, needle0, suffix, period, j, i), X) &&
                match_cond(hay0, needle0, j, needle_len - 1) &&
                shift_table_sound(hay0, needle0, table) &&
                needle == needle@pre &&
                haystack == haystack@pre &&
                needle_len == needle_len@pre &&
                haystack_len == haystack_len@pre &&
                haystack@pre > 0 && needle@pre > 0 &&
                32 < needle_len && needle_len <= haystack_len &&
                haystack_len <= INT_MAX &&

                0 <= j && j <= haystack_len - needle_len &&
                0 < suffix && 0 <= suffix && suffix < needle_len &&
                suffix <= i && i <= needle_len - 1 &&
                0 <= i + j && i + j < haystack_len &&
                0 < period && period <= needle_len &&

                has_permission(&shift) *
                data_at(&pneedle, unsigned char *, needle + i * sizeof(unsigned char)) *
                data_at(&phaystack, unsigned char *, haystack + (i + j) * sizeof(unsigned char)) *
                IntArray::full(shift_table, 256, table) *
                UCharArray::full(haystack, haystack_len, hay0) *
                UCharArray::full(needle, needle_len, needle0)
            */
            while (i < needle_len - 1) // 右侧匹配（并且最后一个字符已匹配） // MARK: modified-original-code
            {
                if (*pneedle != *phaystack)
                    break;
                pneedle = pneedle + 1;
                phaystack = phaystack + 1;
                i = i + 1;
            }
            if (needle_len - 1 <= i)
            {
                /* Match left half. */
                i = suffix - 1;
                pneedle = &needle[i];
                phaystack = &haystack[i + j];
                /*@ Inv Assert
                    exists table,
                    safeExec(ATrue, generic_match_from_left(hay0, needle0, suffix, period, j, 0, i), X) &&
                    shift_table_sound(hay0, needle0, table) &&
                    needle == needle@pre &&
                    haystack == haystack@pre &&
                    needle_len == needle_len@pre &&
                    haystack_len == haystack_len@pre &&
                    haystack@pre > 0 && needle@pre > 0 &&
                    32 < needle_len && needle_len <= haystack_len &&
                    haystack_len <= INT_MAX &&

                    0 <= j && j <= haystack_len - needle_len &&
                    0 < suffix && 0 <= suffix && suffix < needle_len &&
                    0 <= i + 1 && i + 1 <= suffix &&
                    0 <= i + 1 + j && i + 1 + j <= haystack_len &&
                    0 < period && period <= needle_len &&

                    has_permission(&shift) *
                    data_at(&pneedle, unsigned char *, needle + i * sizeof(unsigned char)) *
                    data_at(&phaystack, unsigned char *, haystack + (i + j) * sizeof(unsigned char)) *
                    IntArray::full(shift_table, 256, table) *
                    UCharArray::full(haystack, haystack_len, hay0) *
                    UCharArray::full(needle, needle_len, needle0)
                */
                while (i != ((size_t)-1)) // MARK: modified-original-code
                {
                    if (*pneedle != *phaystack)
                        break;
                    pneedle = pneedle - 1;
                    phaystack = phaystack - 1;
                    i = i - 1;
                }
                if (i == ((size_t)-1))
                    return (void *)(haystack + j);
                j += period;
            }
            else
                j += i - suffix + 1;
        }
    }
    return ((void *)0);
}
