/*
 * Codeforces 1808/A - Lucky Numbers  (rating 900, BRUTE FORCE)
 *
 * Luckiness depends only on the number itself, so tabulate it once for every
 * value up to 10^6 and answer each range with a block-decomposed maximum: full
 * blocks are looked up, the two partial ends are scanned.  The table is built
 * on first use inside solver(), keeping main() free of computation.
 *
 * solver() takes one whole test case (a range) and returns a luckiest number.
 */

// #include <stdio.h>
/* QCP_INSERT_BEGIN:shard03-P007-solver-support */

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard03.P007_1808A_lucky_numbers_lib */
/*@ Extern Coq
      (Luckiness : Z -> Z -> Prop)
      (LuckTable : list Z -> Prop)
      (BlockBestTable : list Z -> list Z -> Prop)
      (Spec : Z -> Z -> Z -> Prop)
*/

/* QCP_INSERT_END:shard03-P007-solver-support */

#define LIMIT 1000001
#define BLK 1024
#define NBLK ((LIMIT + BLK - 1) / BLK)

static signed char luck[LIMIT];
static int blockBest[NBLK];               /* index of the best value per block */
static int built;

/* luckiness: largest digit minus smallest digit of x. */
static int luckiness(int x)
/* QCP_INSERT_BEGIN:shard03-P007-luckiness-contract */
/*@ Require
      1 <= x && x <= 1000000
    Ensure
      Luckiness(x@pre, __return)
*/
/* QCP_INSERT_END:shard03-P007-luckiness-contract */
{
    int hi = 0, lo = 9;
    while (x) {
        int d = x % 10;
        if (d > hi) hi = d;
        if (d < lo) lo = d;
        x /= 10;
    }
    return hi - lo;
}

static void build(void)
/* QCP_INSERT_BEGIN:shard03-P007-build-contract */
/*@ With (luck_before : list Z) (bb_before : list Z) (built_before : Z)
    Require
      CharArray::full(luck, 1000001, luck_before) *
      IntArray::full(blockBest, 977, bb_before) *
      store(&built, int, built_before)
    Ensure
      exists (luck_after : list Z) (bb_after : list Z),
        LuckTable(luck_after) && BlockBestTable(luck_after, bb_after) &&
        CharArray::full(luck, 1000001, luck_after) *
        IntArray::full(blockBest, 977, bb_after) *
        store(&built, int, 1)
*/
/* QCP_INSERT_END:shard03-P007-build-contract */
{
    for (int i = 1; i < LIMIT; i++)
        luck[i] = (signed char)luckiness(i);
    for (int b = 0; b < NBLK; b++) {
        int lo = b * BLK, hi = lo + BLK - 1;
        if (lo == 0)
            lo = 1;
        if (hi >= LIMIT)
            hi = LIMIT - 1;
        int best = lo;
        for (int i = lo; i <= hi; i++)
            if (luck[i] > luck[best])
                best = i;
        blockBest[b] = best;
    }
    built = 1;
}

/* solver: a number in [l, r] of maximum luckiness. */
static int solver(int l, int r)
/* QCP_INSERT_BEGIN:shard03-P007-solver-contract */
/*@ With (luck_before : list Z) (bb_before : list Z) (built_before : Z)
    Require
      1 <= l && l <= r && r <= 1000000 &&
      (built_before == 0 ||
       (LuckTable(luck_before) && BlockBestTable(luck_before, bb_before))) &&
      CharArray::full(luck, 1000001, luck_before) *
      IntArray::full(blockBest, 977, bb_before) *
      store(&built, int, built_before)
    Ensure
      exists (luck_after : list Z) (bb_after : list Z) (built_after : Z),
        Spec(l, r, __return) &&
        LuckTable(luck_after) && BlockBestTable(luck_after, bb_after) &&
        built_after != 0 &&
        CharArray::full(luck, 1000001, luck_after) *
        IntArray::full(blockBest, 977, bb_after) *
        store(&built, int, built_after)
*/
/* QCP_INSERT_END:shard03-P007-solver-contract */
{
    if (!built)
        build();
    int bl = l / BLK, br = r / BLK, best = l;
    if (bl == br) {
        for (int i = l; i <= r; i++)
            if (luck[i] > luck[best])
                best = i;
        return best;
    }
    for (int i = l; i < (bl + 1) * BLK; i++)
        if (luck[i] > luck[best])
            best = i;
    for (int b = bl + 1; b < br; b++)
        if (luck[blockBest[b]] > luck[best])
            best = blockBest[b];
    for (int i = br * BLK; i <= r; i++)
        if (luck[i] > luck[best])
            best = i;
    return best;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         int l, r;
//         scanf("%d %d", &l, &r);
//         printf("%d\n", solver(l, r));
//     }
//     return 0;
// }
