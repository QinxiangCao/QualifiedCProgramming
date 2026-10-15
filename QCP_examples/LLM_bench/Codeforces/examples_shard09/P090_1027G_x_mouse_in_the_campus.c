/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
*/

/*
 * Codeforces 1027/G - X-mouse in the Campus  (rating 2600, NUMBER THEORY)
 *
 * Room r with gcd(r, m) = g stays in that gcd class forever, and multiplying
 * by x acts on r/g inside the units of Z_{m/g}.  So the rooms with a fixed
 * d = m/g form phi(d)/ord_d(x) cycles, each needing one trap, and room 0 needs
 * one more.  Orders multiply through the CRT, so ord_d(x) is the lcm of the
 * orders modulo the prime powers of d, and the divisors of m are enumerated
 * carrying (phi, ord) along.
 */

// #include <stdio.h>
/* QCP_INSERT_BEGIN:shard09-P090-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib */
/*@ Extern Coq
      (Pre : Z -> Z -> Prop)
      (Spec : Z -> Z -> Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P090-solver-support */
/*@ Extern Coq
      (EulerPhi : Z -> Z)
      (Zgcd : Z -> Z -> Z)
      (Ord : Z -> Z -> Z)
      (IsPrime : Z -> Prop)
      (CycleTerm : Z -> Z -> Z)
      (WalkSuffix : list Z -> list Z -> Z -> Z -> Z -> Z)
      (WalkExpSuffix : list Z -> list Z -> Z -> Z -> Z -> Z -> Z)
      (WalkLoopState : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (WalkGlobalBounds : Z -> Z -> Prop)
      (WalkMachineBounds : Z -> Z -> Z -> Z -> Prop)
      (WalkBudget : Z -> Z -> Z -> Prop)
      (WalkPendingState : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (WalkExponentState : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MulLoopState : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (PowLoopState : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (GcdLoopState : Z -> Z -> Z -> Z -> Prop)
      (OrderInput : Z -> Z -> Z -> Prop)
      (OrderResult : Z -> Z -> Z -> Prop)
      (OrderTrialState : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (OrderFactorState : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (OrderStripState : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (FactorPrefix : Z -> Z -> Z -> list Z -> list Z -> Prop)
      (TrialState : Z -> Z -> Z -> list Z -> list Z -> Prop)
      (FactorAtPrime : Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
      (ValidFactorTable : Z -> list Z -> list Z -> Prop)
      (PrefixChoice : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (PrimePowerTransition : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (CycleAnswer : Z -> Z -> Z -> Prop)
      (DivisorCycleSum : Z -> Z -> Z -> Prop)
*/
/*@ Extern Coq
      (OrderTrialStateEx : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (OrderFactorStateEx : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (OrderStripStateEx : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (OrderFinalStateEx : Z -> Z -> Z -> Z -> Z -> Prop)
      (FactorMachineTrialState : Z -> Z -> Z -> list Z -> list Z -> Prop)
      (FactorMachineAtPrime : Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
*/

static unsigned long long pr[64], pe[64];   /* prime factors of m and exponents */
static int nf;

/* mulmod / powmod on 64-bit moduli up to 1e14.
 *
 * mulmod doubles a while walking the bits of b, so no product ever forms: the
 * modulus is at most 1e14, so 2 * modulus still fits an unsigned long long and
 * every intermediate below stays under it. */
static unsigned long long mulmod(unsigned long long a, unsigned long long b,
                                 unsigned long long modulus)
/*@ With (a0 b0 modulus0 : Z)
    Require
      a == a0 && b == b0 && modulus == modulus0 &&
      1 <= modulus0 && modulus0 <= 100000000000000 &&
      0 <= a0 && a0 <= 18446744073709551615 &&
      0 <= b0 && b0 <= 18446744073709551615
    Ensure
      __return == (a0 * b0) % modulus0 &&
      0 <= __return && __return < modulus0
*/
{
    unsigned long long r = 0;
    a %= modulus;
    b %= modulus;
    /*@ Inv Assert
          a0 == a@pre && b0 == b@pre && modulus0 == modulus@pre &&
          modulus == modulus@pre &&
          1 <= modulus@pre && modulus@pre <= 100000000000000 &&
          0 <= a@pre && 0 <= b@pre &&
          0 <= a && a < modulus@pre &&
          0 <= b && b < modulus@pre &&
          0 <= r && r < modulus@pre &&
          MulLoopState(a@pre, b@pre, modulus@pre, a, b, r)
    */
    while (b) {
        if (b & 1) {
            r += a;
            if (r >= modulus)
                r -= modulus;
        }
        a <<= 1;
        if (a >= modulus)
            a -= modulus;
        b >>= 1;
    }
    return r;
}

static unsigned long long powmod(unsigned long long b, unsigned long long e,
                                 unsigned long long modulus)
/*@ With (base exponent modulus0 : Z)
    Require
      b == base && e == exponent && modulus == modulus0 &&
      1 <= modulus0 && modulus0 <= 100000000000000 &&
      0 <= base && base <= 18446744073709551615 &&
      0 <= exponent && exponent <= 100000000000000
    Ensure
      __return == Zpow(base, exponent) % modulus0 &&
      0 <= __return && __return < modulus0
*/
{
    unsigned long long r = 1 % modulus;
    b %= modulus;
    /*@ Inv Assert
          base == b@pre && exponent == e@pre && modulus0 == modulus@pre &&
          modulus == modulus@pre &&
          1 <= modulus@pre && modulus@pre <= 100000000000000 &&
          0 <= base &&
          0 <= b && b < modulus@pre &&
          0 <= e && e <= exponent &&
          0 <= r && r < modulus@pre &&
          PowLoopState(base, exponent, modulus@pre, b, e, r)
    */
    while (e) {
        if (e & 1)
            r = mulmod(r, b, modulus) /*@ where a0 = r, b0 = b, modulus0 = modulus */;
        b = mulmod(b, b, modulus) /*@ where a0 = b, b0 = b, modulus0 = modulus */;
        e >>= 1;
    }
    return r;
}

static unsigned long long gcd_(unsigned long long a, unsigned long long b)
/*@ With (a0 b0 : Z)
    Require
      a == a0 && b == b0 &&
      0 <= a0 && a0 <= 100000000000000 &&
      0 <= b0 && b0 <= 100000000000000
    Ensure
      __return == Zgcd(a0, b0) &&
      0 <= __return && __return <= a0 + b0
*/
{
    /*@ Inv Assert
          a0 == a@pre && b0 == b@pre &&
          0 <= a0 && 0 <= b0 &&
          0 <= a && a <= 100000000000000 &&
          0 <= b && b <= 100000000000000 &&
          GcdLoopState(a0, b0, a, b)
    */
    while (b) {
        unsigned long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* order: multiplicative order of x modulo mod, given phi(mod). */
static unsigned long long order(unsigned long long x, unsigned long long modulus,
                                unsigned long long phi)
/*@ With (x0 modulus0 phi0 : Z)
    Require
      x == x0 && modulus == modulus0 && phi == phi0 &&
      modulus0 <= 100000000000000 &&
      OrderInput(x0, modulus0, phi0)
    Ensure
      OrderResult(x0, modulus0, __return)
*/
{
    if (modulus == 1)
        return 1;
    unsigned long long ord = phi, t = phi;
    /*@ Inv Assert
          x0 == x@pre && modulus0 == modulus@pre && phi0 == phi@pre &&
          x == x@pre && modulus == modulus@pre && phi == phi@pre &&
          1 < modulus@pre && modulus@pre <= 100000000000000 &&
          2 <= q && q <= 10000001 &&
          0 < t && t <= phi@pre &&
          0 < ord && ord <= phi@pre &&
          OrderTrialStateEx(x@pre, modulus@pre, phi@pre, q, t, ord)
    */
    for (unsigned long long q = 2; q * q <= t; q++)
        if (t % q == 0) {
            /*@ Inv Assert
                  x0 == x@pre && modulus0 == modulus@pre && phi0 == phi@pre &&
                  x == x@pre && modulus == modulus@pre && phi == phi@pre &&
                  1 < modulus@pre && modulus@pre <= 100000000000000 &&
                  2 <= q && q <= 10000000 &&
                  0 < t && t <= phi@pre &&
                  0 < ord && ord <= phi@pre &&
                  OrderFactorStateEx(x@pre, modulus@pre, phi@pre, q, t, ord)
            */
            while (t % q == 0)
                t /= q;
            /*@ Inv Assert
                  x0 == x@pre && modulus0 == modulus@pre && phi0 == phi@pre &&
                  x == x@pre && modulus == modulus@pre && phi == phi@pre &&
                  1 < modulus@pre && modulus@pre <= 100000000000000 &&
                  2 <= q && q <= 10000000 &&
                  0 < t && t <= phi@pre &&
                  0 < ord && ord <= phi@pre &&
                  OrderStripStateEx(x@pre, modulus@pre, phi@pre, q, t, ord)
            */
            while (ord % q == 0 && powmod(x, ord / q, modulus) == 1)
                ord /= q;
        }
    if (t > 1)
        /*@ Inv Assert
              x0 == x@pre && modulus0 == modulus@pre && phi0 == phi@pre &&
              x == x@pre && modulus == modulus@pre && phi == phi@pre &&
              1 < modulus@pre && modulus@pre <= 100000000000000 &&
              1 < t && t <= phi@pre &&
              0 < ord && ord <= phi@pre &&
              OrderFinalStateEx(x@pre, modulus@pre, phi@pre, t, ord)
        */
        while (ord % t == 0 && powmod(x, ord / t, modulus) == 1)
            ord /= t;
    return ord;
}

static unsigned long long x_, total_;

/* walk: enumerate the divisors of m, carrying phi(d) and ord_d(x). */
static void walk(int i, unsigned long long d, unsigned long long phi,
                 unsigned long long ord)
/*@ With (m x_value factor_count before : Z) (pr_values pe_values : list Z)
    Require
      Zlength(pr_values) == factor_count &&
      Zlength(pe_values) == factor_count &&
      0 <= i && i <= factor_count &&
      WalkGlobalBounds(m, x_value) &&
      WalkMachineBounds(m, d, phi, ord) && 0 < ord &&
      ValidFactorTable(m, pr_values, pe_values) &&
      PrefixChoice(pr_values, pe_values, x_value, i, d, phi, ord) &&
      WalkBudget(m, before, WalkSuffix(pr_values, pe_values, x_value, i, d)) &&
      UInt64Array::seg(pr, 0, factor_count, pr_values) *
      UInt64Array::undef_seg(pr, factor_count, 64) *
      UInt64Array::seg(pe, 0, factor_count, pe_values) *
      UInt64Array::undef_seg(pe, factor_count, 64) *
      store_int(&nf, factor_count) * store(&x_, x_value) * store(&total_, before)
    Ensure
      UInt64Array::seg(pr, 0, factor_count, pr_values) *
      UInt64Array::undef_seg(pr, factor_count, 64) *
      UInt64Array::seg(pe, 0, factor_count, pe_values) *
      UInt64Array::undef_seg(pe, factor_count, 64) *
      store_int(&nf, factor_count) * store(&x_, x_value) *
      store(&total_, before + WalkSuffix(pr_values, pe_values, x_value, i, d))
*/
{
    if (i == nf) {
        if (d > 1)
            total_ += phi / ord;
        return;
    }
    /*@ Assert
          Zlength(pr_values) == factor_count &&
          Zlength(pe_values) == factor_count &&
          i == i@pre && d == d@pre && phi == phi@pre && ord == ord@pre &&
          0 <= i && i < factor_count &&
          WalkGlobalBounds(m, x_value) &&
          WalkMachineBounds(m, d, phi, ord) && 0 < ord &&
          ValidFactorTable(m, pr_values, pe_values) &&
          PrefixChoice(pr_values, pe_values, x_value, i, d, phi, ord) &&
          PrefixChoice(pr_values, pe_values, x_value, i + 1, d, phi, ord) &&
          WalkBudget(m, before, WalkSuffix(pr_values, pe_values, x_value, i, d)) &&
          WalkBudget(m, before, WalkSuffix(pr_values, pe_values, x_value, i + 1, d)) &&
          UInt64Array::seg(pr, 0, factor_count, pr_values) *
          UInt64Array::undef_seg(pr, factor_count, 64) *
          UInt64Array::seg(pe, 0, factor_count, pe_values) *
          UInt64Array::undef_seg(pe, factor_count, 64) *
          store_int(&nf, factor_count) * store(&x_, x_value) * store(&total_, before)
    */
    walk(i + 1, d, phi, ord)              /* exponent 0 */
      /*@ where m = m, x_value = x_value, factor_count = factor_count,
                  pr_values = pr_values, pe_values = pe_values, before = before */;
    /*@ Assert
          Zlength(pr_values) == factor_count &&
          Zlength(pe_values) == factor_count &&
          i == i@pre && d == d@pre && phi == phi@pre && ord == ord@pre &&
          0 <= i && i < factor_count &&
          WalkGlobalBounds(m, x_value) &&
          WalkMachineBounds(m, d, phi, ord) && 0 < ord &&
          ValidFactorTable(m, pr_values, pe_values) &&
          PrefixChoice(pr_values, pe_values, x_value, i, d, phi, ord) &&
          WalkBudget(m, before, WalkSuffix(pr_values, pe_values, x_value, i, d)) &&
          WalkPendingState(pr_values, pe_values, m, x_value, i, d, before,
                           before + WalkSuffix(pr_values, pe_values, x_value, i + 1, d), 1) &&
          UInt64Array::seg(pr, 0, factor_count, pr_values) *
          UInt64Array::undef_seg(pr, factor_count, 64) *
          UInt64Array::seg(pe, 0, factor_count, pe_values) *
          UInt64Array::undef_seg(pe, factor_count, 64) *
          store_int(&nf, factor_count) * store(&x_, x_value) *
          store(&total_, before + WalkSuffix(pr_values, pe_values, x_value, i + 1, d))
    */
    unsigned long long p = pr[i], pk = 1, ph = 1;
    /*@ Inv Assert
          exists (current : Z),
            Zlength(pr_values) == factor_count &&
            Zlength(pe_values) == factor_count &&
            i == i@pre && d == d@pre && phi == phi@pre && ord == ord@pre &&
            0 <= i && i < factor_count &&
            1 <= e && e <= pe_values[i] + 1 &&
            p == pr_values[i] &&
            WalkExponentState(m, p, e, pe_values[i], pk, ph) &&
            WalkGlobalBounds(m, x_value) &&
            WalkMachineBounds(m, d, phi, ord) && 0 < ord &&
            ValidFactorTable(m, pr_values, pe_values) &&
            PrefixChoice(pr_values, pe_values, x_value, i, d, phi, ord) &&
            WalkPendingState(pr_values, pe_values, m, x_value, i, d,
                             before, current, e) &&
            UInt64Array::seg(pr, 0, factor_count, pr_values) *
            UInt64Array::undef_seg(pr, factor_count, 64) *
            UInt64Array::seg(pe, 0, factor_count, pe_values) *
            UInt64Array::undef_seg(pe, factor_count, 64) *
            store_int(&nf, factor_count) * store(&x_, x_value) * store(&total_, current)
    */
    for (unsigned long long e = 1; e <= pe[i]; e++) {
        pk *= p;
        ph = (e == 1) ? p - 1 : ph * p;
        /*@ Assert
              exists (current : Z),
                Zlength(pr_values) == factor_count &&
                Zlength(pe_values) == factor_count &&
                i == i@pre && d == d@pre && phi == phi@pre && ord == ord@pre &&
                0 <= i && i < factor_count &&
                1 <= e && e <= pe_values[i] &&
                p == pr_values[i] &&
                WalkExponentState(m, p, e + 1, pe_values[i], pk, ph) &&
                OrderInput(x_value % pk, pk, ph) &&
                WalkGlobalBounds(m, x_value) &&
                WalkMachineBounds(m, d, phi, ord) && 0 < ord &&
                ValidFactorTable(m, pr_values, pe_values) &&
                PrefixChoice(pr_values, pe_values, x_value, i, d, phi, ord) &&
                WalkPendingState(pr_values, pe_values, m, x_value, i, d,
                                 before, current, e) &&
                UInt64Array::seg(pr, 0, factor_count, pr_values) *
                UInt64Array::undef_seg(pr, factor_count, 64) *
                UInt64Array::seg(pe, 0, factor_count, pe_values) *
                UInt64Array::undef_seg(pe, factor_count, 64) *
                store_int(&nf, factor_count) * store(&x_, x_value) * store(&total_, current)
        */
        unsigned long long o = order(x_ % pk, pk, ph)
          /*@ where x0 = x_value % pk, modulus0 = pk, phi0 = ph */;
        unsigned long long g = gcd_(ord, o) /*@ where a0 = ord, b0 = o */;
        /*@ Assert
              exists (current : Z),
                Zlength(pr_values) == factor_count &&
                Zlength(pe_values) == factor_count &&
                i == i@pre && d == d@pre && phi == phi@pre && ord == ord@pre &&
                0 <= i && i < factor_count &&
                1 <= e && e <= pe_values[i] &&
                p == pr_values[i] && 0 < g &&
                WalkGlobalBounds(m, x_value) &&
                WalkMachineBounds(m, d, phi, ord) && 0 < ord &&
                ValidFactorTable(m, pr_values, pe_values) &&
                PrefixChoice(pr_values, pe_values, x_value, i, d, phi, ord) &&
                WalkExponentState(m, p, e + 1, pe_values[i], pk, ph) &&
                WalkMachineBounds(m, d * pk, phi * ph, ord / g * o) &&
                PrimePowerTransition(x_value, d, phi, ord, p, e, pk, ph, o, g,
                                     d * pk, phi * ph, ord / g * o) &&
                PrefixChoice(pr_values, pe_values, x_value, i + 1,
                             d * pk, phi * ph, ord / g * o) &&
                WalkBudget(m, current,
                           WalkSuffix(pr_values, pe_values, x_value, i + 1, d * pk)) &&
                WalkPendingState(pr_values, pe_values, m, x_value, i, d,
                                 before, current, e) &&
                UInt64Array::seg(pr, 0, factor_count, pr_values) *
                UInt64Array::undef_seg(pr, factor_count, 64) *
                UInt64Array::seg(pe, 0, factor_count, pe_values) *
                UInt64Array::undef_seg(pe, factor_count, 64) *
                store_int(&nf, factor_count) * store(&x_, x_value) * store(&total_, current)
        */
        walk(i + 1, d * pk, phi * ph, ord / g * o)
          /*@ where m = m, x_value = x_value, factor_count = factor_count,
                      pr_values = pr_values, pe_values = pe_values, before = total_ */;
    }
}

/* solver: minimum number of traps. */
static unsigned long long solver(unsigned long long m, unsigned long long x)
/* QCP_INSERT_BEGIN:shard09-P090-solver-contract */
/*@
    Require
      2 <= m && m <= 100000000000000 && 1 <= x && x < m &&
      Pre(m, x) &&
      UInt64Array::undef_full(pr, 64) * UInt64Array::undef_full(pe, 64) *
      has_int_permission(&nf) * has_permission(&x_) * has_permission(&total_)
    Ensure
      Spec(m, x, __return) &&
      exists (factor_count : Z) (base : Z) (accumulator : Z),
        0 <= factor_count && factor_count <= 64 &&
        UInt64Array::seg_shape(pr, 0, factor_count) *
        UInt64Array::undef_seg(pr, factor_count, 64) *
        UInt64Array::seg_shape(pe, 0, factor_count) *
        UInt64Array::undef_seg(pe, factor_count, 64) *
        store_int(&nf, factor_count) * store(&x_, base) * store(&total_, accumulator)
*/
/* QCP_INSERT_END:shard09-P090-solver-contract */
{
    unsigned long long t = m;
    nf = 0;
    /*@ Inv Assert
          exists (factor_count remainder : Z) (pr_values pe_values : list Z),
            m == m@pre && x == x@pre &&
            2 <= m@pre && m@pre <= 100000000000000 &&
            1 <= x@pre && x@pre < m@pre && Pre(m@pre, x@pre) &&
            2 <= p && p <= 10000001 &&
            0 <= factor_count && factor_count < 64 &&
            Zlength(pr_values) == factor_count &&
            Zlength(pe_values) == factor_count &&
            0 < remainder && remainder <= m@pre &&
            FactorMachineTrialState(m@pre, p, remainder, pr_values, pe_values) &&
            UInt64Array::seg(pr, 0, factor_count, pr_values) *
            UInt64Array::undef_seg(pr, factor_count, 64) *
            UInt64Array::seg(pe, 0, factor_count, pe_values) *
            UInt64Array::undef_seg(pe, factor_count, 64) *
            store_int(&nf, factor_count) * store(&t, remainder) *
            has_permission(&x_) * has_permission(&total_)
    */
    for (unsigned long long p = 2; p * p <= t; p++)
        if (t % p == 0) {
            pr[nf] = p;
            pe[nf] = 0;
            /*@ Inv Assert
                  exists (factor_count original_remainder remainder exponent : Z)
                         (pr_values pe_values : list Z),
                    m == m@pre && x == x@pre &&
                    2 <= m@pre && m@pre <= 100000000000000 &&
                    1 <= x@pre && x@pre < m@pre && Pre(m@pre, x@pre) &&
                    2 <= p && p <= 10000000 &&
                    0 <= factor_count && factor_count < 64 &&
                    Zlength(pr_values) == factor_count &&
                    Zlength(pe_values) == factor_count &&
                    0 <= exponent && exponent <= 47 &&
                    FactorMachineAtPrime(m@pre, p, original_remainder,
                                         remainder, exponent, pr_values, pe_values) &&
                    UInt64Array::seg(pr, 0, factor_count, pr_values) *
                    UInt64Array::seg(pr, factor_count, factor_count + 1, cons(p, nil)) *
                    UInt64Array::undef_seg(pr, factor_count + 1, 64) *
                    UInt64Array::seg(pe, 0, factor_count, pe_values) *
                    UInt64Array::seg(pe, factor_count, factor_count + 1, cons(exponent, nil)) *
                    UInt64Array::undef_seg(pe, factor_count + 1, 64) *
                    store_int(&nf, factor_count) * store(&t, remainder) *
                    has_permission(&x_) * has_permission(&total_)
            */
            while (t % p == 0) {
                t /= p;
                pe[nf] = pe[nf] + 1;
            }
            nf++;
        }
    if (t > 1) {
        pr[nf] = t;
        { pe[nf] = 1; nf++; }
    }
    /*@ Assert
          exists (factor_count remainder : Z) (pr_values pe_values : list Z),
            m == m@pre && x == x@pre &&
            2 <= m@pre && m@pre <= 100000000000000 &&
            1 <= x@pre && x@pre < m@pre && Pre(m@pre, x@pre) &&
            0 <= factor_count && factor_count <= 64 &&
            Zlength(pr_values) == factor_count &&
            Zlength(pe_values) == factor_count &&
            ValidFactorTable(m@pre, pr_values, pe_values) &&
            UInt64Array::seg(pr, 0, factor_count, pr_values) *
            UInt64Array::undef_seg(pr, factor_count, 64) *
            UInt64Array::seg(pe, 0, factor_count, pe_values) *
            UInt64Array::undef_seg(pe, factor_count, 64) *
            store_int(&nf, factor_count) * store(&t, remainder) *
            has_permission(&x_) * has_permission(&total_)
    */
    /*@ Assert
          exists (factor_count remainder : Z) (pr_values pe_values : list Z),
            m == m@pre && x == x@pre &&
            2 <= m@pre && m@pre <= 100000000000000 &&
            1 <= x@pre && x@pre < m@pre && Pre(m@pre, x@pre) &&
            0 <= factor_count && factor_count <= 64 &&
            Zlength(pr_values) == factor_count &&
            Zlength(pe_values) == factor_count &&
            ValidFactorTable(m@pre, pr_values, pe_values) &&
            PrefixChoice(pr_values, pe_values, x@pre, 0, 1, 1, 1) &&
            0 <= WalkSuffix(pr_values, pe_values, x@pre, 0, 1) &&
            WalkSuffix(pr_values, pe_values, x@pre, 0, 1) <= m@pre &&
            UInt64Array::seg(pr, 0, factor_count, pr_values) *
            UInt64Array::undef_seg(pr, factor_count, 64) *
            UInt64Array::seg(pe, 0, factor_count, pe_values) *
            UInt64Array::undef_seg(pe, factor_count, 64) *
            store_int(&nf, factor_count) * store(&t, remainder) *
            has_permission(&x_) * has_permission(&total_)
    */
    x_ = x;
    total_ = 0;
    walk(0, 1, 1, 1)
      /*@ where m = m, x_value = x, before = 0 */;
    /*@ Assert
          exists (factor_count remainder accumulator : Z)
                 (pr_values pe_values : list Z),
            m == m@pre && x == x@pre &&
            2 <= m@pre && m@pre <= 100000000000000 &&
            1 <= x@pre && x@pre < m@pre && Pre(m@pre, x@pre) &&
            0 <= factor_count && factor_count <= 64 &&
            Zlength(pr_values) == factor_count &&
            Zlength(pe_values) == factor_count &&
            ValidFactorTable(m@pre, pr_values, pe_values) &&
            accumulator == WalkSuffix(pr_values, pe_values, x@pre, 0, 1) &&
            CycleAnswer(m@pre, x@pre, accumulator) &&
            UInt64Array::seg(pr, 0, factor_count, pr_values) *
            UInt64Array::undef_seg(pr, factor_count, 64) *
            UInt64Array::seg(pe, 0, factor_count, pe_values) *
            UInt64Array::undef_seg(pe, factor_count, 64) *
            store_int(&nf, factor_count) * store(&t, remainder) *
            store(&x_, x@pre) * store(&total_, accumulator)
    */
    return total_ + 1;                    /* room 0 */
}

// int main(void)
// {
//     unsigned long long m, x;
//     if (scanf("%llu %llu", &m, &x) != 2)
//         return 0;
//     printf("%llu\n", solver(m, x));
//     return 0;
// }
