/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
*/

/*
 * Codeforces 1594/D - The Number of Imposters  (rating 1700, GRAPHS)
 *
 * "crewmate" forces the two players into the same role, "imposter" into
 * different ones, so each comment is a parity edge.  Two-colour every
 * component: contradictions mean -1, otherwise the component contributes the
 * larger of its two colour classes.
 */

// #include <stdio.h>

/* QCP_INSERT_BEGIN:shard09-P053-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib */
/*@ Extern Coq
      (fst : {A B} -> A * B -> A)
      (snd : {A B} -> A * B -> B)
      (Spec : Z -> list(Z*Z*Z) -> Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P053-solver-support */

/*@ Extern Coq
      (ForwardStar : Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list(Z*Z*Z) -> Prop)
      (ForwardStarRanges : Z -> Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (HeadsInitialised : list Z -> Z -> Prop)
      (ColoursInitialised : list Z -> Z -> Prop)
      (ColourValues : Z -> list Z -> Prop)
      (ParityRespected : list(Z*Z*Z) -> list Z -> Prop)
      (ColouredClosed : list(Z*Z*Z) -> list Z -> Prop)
      (MaxImpostersOn : Z -> list(Z*Z*Z) -> list Z -> Z -> Prop)
      (ComponentFrontier : Z -> list(Z*Z*Z) -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (ComponentScan : Z -> list(Z*Z*Z) -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
      (ComponentComplete : Z -> list(Z*Z*Z) -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
*/

/*@ Extern Coq
      (ComponentFrontierStrong : Z -> list(Z*Z*Z) -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (ComponentScanStrong : Z -> list(Z*Z*Z) -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
      (ComponentCompleteStrong : Z -> list(Z*Z*Z) -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
*/

#define MAXN 200005
#define MAXM 500005

/* solver: maximum number of imposters over n players, or -1 on contradiction. */
static long long solver(int n, int m,
                        const int *comment_u, const int *comment_v,
                        const int *comment_diff,
                        int *head, int *nxt, int *to, int *wt,
                        int *color, int *stack_)
/* QCP_INSERT_BEGIN:shard09-P053-normalized-solver-contract */
/*@ With (comments : list(Z*Z*Z)) (comment_sources : list Z) (comment_targets : list Z) (comment_kinds : list Z)
    Require
      1 <= n && n <= 200000 &&
      m <= 500000 && (forall i, (0 <= i && i < m) => (1 <= fst(fst(comments[i])) && fst(fst(comments[i])) <= n && 1 <= snd(fst(comments[i])) && snd(fst(comments[i])) <= n && fst(fst(comments[i])) != snd(fst(comments[i])) && (snd(comments[i]) == 0 || snd(comments[i]) == 1))) && m == Zlength(comments) && Zlength(comment_sources) == m && Zlength(comment_targets) == m && Zlength(comment_kinds) == m && (forall i, (0 <= i && i < m) => (comment_sources[i] == fst(fst(comments[i])) && comment_targets[i] == snd(fst(comments[i])) && comment_kinds[i] == snd(comments[i]))) && IntArray::full(comment_u, m, comment_sources) * IntArray::full(comment_v, m, comment_targets) * IntArray::full(comment_diff, m, comment_kinds) * IntArray::full_shape(head, n + 1) * IntArray::full_shape(nxt, 2 * m) * IntArray::full_shape(to, 2 * m) * IntArray::full_shape(wt, 2 * m) * IntArray::full_shape(color, n + 1) * IntArray::full_shape(stack_, n + 1)
    Ensure
      Spec(n, comments, __return) && IntArray::full_shape(comment_u, m) * IntArray::full_shape(comment_v, m) * IntArray::full_shape(comment_diff, m) * IntArray::full_shape(head, n + 1) * IntArray::full_shape(nxt, 2 * m) * IntArray::full_shape(to, 2 * m) * IntArray::full_shape(wt, 2 * m) * IntArray::full_shape(color, n + 1) * IntArray::full_shape(stack_, n + 1)
*/
/* QCP_INSERT_END:shard09-P053-normalized-solver-contract */
{
    /*@ Inv Assert
          exists hs ns ts ws cs ks,
            n == n@pre && m == m@pre &&
            comment_u == comment_u@pre && comment_v == comment_v@pre &&
            comment_diff == comment_diff@pre &&
            head == head@pre && nxt == nxt@pre && to == to@pre && wt == wt@pre &&
            color == color@pre && stack_ == stack_@pre &&
            1 <= n@pre && n@pre <= 200000 && 0 <= m@pre && m@pre <= 500000 &&
            m@pre == Zlength(comments) &&
            Zlength(comment_sources) == m@pre && Zlength(comment_targets) == m@pre &&
            Zlength(comment_kinds) == m@pre &&
            (forall i, (0 <= i && i < m@pre) =>
              (1 <= fst(fst(comments[i])) && fst(fst(comments[i])) <= n@pre &&
               1 <= snd(fst(comments[i])) && snd(fst(comments[i])) <= n@pre &&
               fst(fst(comments[i])) != snd(fst(comments[i])) &&
               (snd(comments[i]) == 0 || snd(comments[i]) == 1) &&
               comment_sources[i] == fst(fst(comments[i])) &&
               comment_targets[i] == snd(fst(comments[i])) &&
               comment_kinds[i] == snd(comments[i]))) &&
            1 <= v && v <= n@pre + 1 &&
            Zlength(hs) == n@pre + 1 && Zlength(ns) == 2 * m@pre &&
            Zlength(ts) == 2 * m@pre && Zlength(ws) == 2 * m@pre &&
            Zlength(cs) == n@pre + 1 && Zlength(ks) == n@pre + 1 &&
            HeadsInitialised(hs, v) &&
            IntArray::full(comment_u@pre, m@pre, comment_sources) *
            IntArray::full(comment_v@pre, m@pre, comment_targets) *
            IntArray::full(comment_diff@pre, m@pre, comment_kinds) *
            IntArray::full(head@pre, n@pre + 1, hs) *
            IntArray::full(nxt@pre, 2 * m@pre, ns) *
            IntArray::full(to@pre, 2 * m@pre, ts) *
            IntArray::full(wt@pre, 2 * m@pre, ws) *
            IntArray::full(color@pre, n@pre + 1, cs) *
            IntArray::full(stack_@pre, n@pre + 1, ks)
    */
    for (int v = 1; v <= n; v++)
        head[v] = -1;
    /*@ Inv Assert
          exists hs ns ts ws cs ks,
            n == n@pre && m == m@pre &&
            comment_u == comment_u@pre && comment_v == comment_v@pre &&
            comment_diff == comment_diff@pre &&
            head == head@pre && nxt == nxt@pre && to == to@pre && wt == wt@pre &&
            color == color@pre && stack_ == stack_@pre &&
            1 <= n@pre && n@pre <= 200000 && 0 <= m@pre && m@pre <= 500000 &&
            m@pre == Zlength(comments) &&
            Zlength(comment_sources) == m@pre && Zlength(comment_targets) == m@pre &&
            Zlength(comment_kinds) == m@pre &&
            (forall q, (0 <= q && q < m@pre) =>
              (1 <= comment_sources[q] && comment_sources[q] <= n@pre &&
               1 <= comment_targets[q] && comment_targets[q] <= n@pre &&
               comment_sources[q] != comment_targets[q] &&
               (comment_kinds[q] == 0 || comment_kinds[q] == 1) &&
               comment_sources[q] == fst(fst(comments[q])) &&
               comment_targets[q] == snd(fst(comments[q])) &&
               comment_kinds[q] == snd(comments[q]))) &&
            0 <= i && i <= m@pre &&
            ((i < m@pre) =>
              (1 <= comment_sources[i] && comment_sources[i] <= n@pre &&
               1 <= comment_targets[i] && comment_targets[i] <= n@pre &&
               (comment_kinds[i] == 0 || comment_kinds[i] == 1))) &&
            ForwardStar(n@pre, m@pre, i, hs, ns, ts, ws, comments) &&
            ForwardStarRanges(n@pre, i, hs, ns, ts, ws) &&
            Zlength(cs) == n@pre + 1 && Zlength(ks) == n@pre + 1 &&
            IntArray::full(comment_u@pre, m@pre, comment_sources) *
            IntArray::full(comment_v@pre, m@pre, comment_targets) *
            IntArray::full(comment_diff@pre, m@pre, comment_kinds) *
            IntArray::full(head@pre, n@pre + 1, hs) *
            IntArray::full(nxt@pre, 2 * m@pre, ns) *
            IntArray::full(to@pre, 2 * m@pre, ts) *
            IntArray::full(wt@pre, 2 * m@pre, ws) *
            IntArray::full(color@pre, n@pre + 1, cs) *
            IntArray::full(stack_@pre, n@pre + 1, ks)
    */
    for (int i = 0; i < m; i++) {
        int e = 2 * i, u = comment_u[i], v = comment_v[i];
        to[e] = v; wt[e] = comment_diff[i]; nxt[e] = head[u]; head[u] = e;
        to[e + 1] = u; wt[e + 1] = comment_diff[i];
        nxt[e + 1] = head[v]; head[v] = e + 1;
    }
    /*@ Inv Assert
          exists hs ns ts ws cs ks,
            n == n@pre && m == m@pre &&
            comment_u == comment_u@pre && comment_v == comment_v@pre &&
            comment_diff == comment_diff@pre &&
            head == head@pre && nxt == nxt@pre && to == to@pre && wt == wt@pre &&
            color == color@pre && stack_ == stack_@pre &&
            1 <= n@pre && n@pre <= 200000 && 0 <= m@pre && m@pre <= 500000 &&
            m@pre == Zlength(comments) &&
            Zlength(comment_sources) == m@pre && Zlength(comment_targets) == m@pre &&
            Zlength(comment_kinds) == m@pre &&
            (forall q, (0 <= q && q < m@pre) =>
              (1 <= comment_sources[q] && comment_sources[q] <= n@pre &&
               1 <= comment_targets[q] && comment_targets[q] <= n@pre &&
               comment_sources[q] != comment_targets[q] &&
               (comment_kinds[q] == 0 || comment_kinds[q] == 1) &&
               comment_sources[q] == fst(fst(comments[q])) &&
               comment_targets[q] == snd(fst(comments[q])) &&
               comment_kinds[q] == snd(comments[q]))) &&
            1 <= v && v <= n@pre + 1 &&
            ForwardStar(n@pre, m@pre, m@pre, hs, ns, ts, ws, comments) &&
            ForwardStarRanges(n@pre, m@pre, hs, ns, ts, ws) &&
            Zlength(cs) == n@pre + 1 && Zlength(ks) == n@pre + 1 &&
            ColoursInitialised(cs, v) &&
            IntArray::full(comment_u@pre, m@pre, comment_sources) *
            IntArray::full(comment_v@pre, m@pre, comment_targets) *
            IntArray::full(comment_diff@pre, m@pre, comment_kinds) *
            IntArray::full(head@pre, n@pre + 1, hs) *
            IntArray::full(nxt@pre, 2 * m@pre, ns) *
            IntArray::full(to@pre, 2 * m@pre, ts) *
            IntArray::full(wt@pre, 2 * m@pre, ws) *
            IntArray::full(color@pre, n@pre + 1, cs) *
            IntArray::full(stack_@pre, n@pre + 1, ks)
    */
    for (int v = 1; v <= n; v++)
        color[v] = -1;
    long long total = 0;
    /*@ Inv Assert
          exists hs ns ts ws cs ks,
            n == n@pre && m == m@pre &&
            comment_u == comment_u@pre && comment_v == comment_v@pre &&
            comment_diff == comment_diff@pre &&
            head == head@pre && nxt == nxt@pre && to == to@pre && wt == wt@pre &&
            color == color@pre && stack_ == stack_@pre &&
            1 <= n@pre && n@pre <= 200000 && 0 <= m@pre && m@pre <= 500000 &&
            m@pre == Zlength(comments) &&
            Zlength(comment_sources) == m@pre && Zlength(comment_targets) == m@pre &&
            Zlength(comment_kinds) == m@pre &&
            (forall q, (0 <= q && q < m@pre) =>
              (1 <= comment_sources[q] && comment_sources[q] <= n@pre &&
               1 <= comment_targets[q] && comment_targets[q] <= n@pre &&
               comment_sources[q] != comment_targets[q] &&
               (comment_kinds[q] == 0 || comment_kinds[q] == 1) &&
               comment_sources[q] == fst(fst(comments[q])) &&
               comment_targets[q] == snd(fst(comments[q])) &&
               comment_kinds[q] == snd(comments[q]))) &&
            1 <= s && s <= n@pre + 1 && 0 <= total && total <= n@pre &&
            ForwardStar(n@pre, m@pre, m@pre, hs, ns, ts, ws, comments) &&
            ForwardStarRanges(n@pre, m@pre, hs, ns, ts, ws) &&
            ColourValues(n@pre, cs) && ParityRespected(comments, cs) &&
            ColouredClosed(comments, cs) &&
            MaxImpostersOn(n@pre, comments, cs, total) &&
            (forall v, (1 <= v && v < s) => cs[v] != -1) &&
            Zlength(ks) == n@pre + 1 &&
            IntArray::full(comment_u@pre, m@pre, comment_sources) *
            IntArray::full(comment_v@pre, m@pre, comment_targets) *
            IntArray::full(comment_diff@pre, m@pre, comment_kinds) *
            IntArray::full(head@pre, n@pre + 1, hs) *
            IntArray::full(nxt@pre, 2 * m@pre, ns) *
            IntArray::full(to@pre, 2 * m@pre, ts) *
            IntArray::full(wt@pre, 2 * m@pre, ws) *
            IntArray::full(color@pre, n@pre + 1, cs) *
            IntArray::full(stack_@pre, n@pre + 1, ks)
    */
    for (int s = 1; s <= n; s++) {
        if (color[s] >= 0)
            continue;
        int top = 0;
        color[s] = 0;
        { stack_[top] = s; top++; }
        int c0 = 0, c1 = 0;
        /*@ Inv Assert
              exists hs ns ts ws before cs ks finished,
                n == n@pre && m == m@pre &&
                comment_u == comment_u@pre && comment_v == comment_v@pre &&
                comment_diff == comment_diff@pre &&
                head == head@pre && nxt == nxt@pre && to == to@pre && wt == wt@pre &&
                color == color@pre && stack_ == stack_@pre &&
                1 <= n@pre && n@pre <= 200000 && 0 <= m@pre && m@pre <= 500000 &&
                m@pre == Zlength(comments) &&
                Zlength(comment_sources) == m@pre && Zlength(comment_targets) == m@pre &&
                Zlength(comment_kinds) == m@pre &&
                (forall q, (0 <= q && q < m@pre) =>
                  (1 <= comment_sources[q] && comment_sources[q] <= n@pre &&
                   1 <= comment_targets[q] && comment_targets[q] <= n@pre &&
                   comment_sources[q] != comment_targets[q] &&
                   (comment_kinds[q] == 0 || comment_kinds[q] == 1) &&
                   comment_sources[q] == fst(fst(comments[q])) &&
                   comment_targets[q] == snd(fst(comments[q])) &&
                   comment_kinds[q] == snd(comments[q]))) &&
                1 <= s && s <= n@pre && 0 <= total && total <= n@pre &&
                0 <= top && top <= n@pre &&
                0 <= c0 && 0 <= c1 && c0 + c1 <= n@pre &&
                (forall j, (0 <= j && j < top) =>
                   (1 <= ks[j] && ks[j] <= n@pre)) &&
                Zlength(before) == n@pre + 1 && Zlength(ks) == n@pre + 1 &&
                ColourValues(n@pre, before) && ParityRespected(comments, before) &&
                ColouredClosed(comments, before) &&
                MaxImpostersOn(n@pre, comments, before, total) &&
                (forall v, (1 <= v && v < s) => before[v] != -1) &&
                before[s] == -1 &&
                cs[s] != -1 &&
                ComponentFrontierStrong(n@pre, comments, before, cs, finished,
                                        sublist(0, top, ks), c0, c1) &&
                ForwardStar(n@pre, m@pre, m@pre, hs, ns, ts, ws, comments) &&
                ForwardStarRanges(n@pre, m@pre, hs, ns, ts, ws) &&
                IntArray::full(comment_u@pre, m@pre, comment_sources) *
                IntArray::full(comment_v@pre, m@pre, comment_targets) *
                IntArray::full(comment_diff@pre, m@pre, comment_kinds) *
                IntArray::full(head@pre, n@pre + 1, hs) *
                IntArray::full(nxt@pre, 2 * m@pre, ns) *
                IntArray::full(to@pre, 2 * m@pre, ts) *
                IntArray::full(wt@pre, 2 * m@pre, ws) *
                IntArray::full(color@pre, n@pre + 1, cs) *
                IntArray::full(stack_@pre, n@pre + 1, ks)
        */
        while (top) {
            top--;
            int u = stack_[top];
            if (color[u] == 0) c0++; else c1++;
            /*@ Inv Assert
                  exists hs ns ts ws before cs ks finished,
                    n == n@pre && m == m@pre &&
                    comment_u == comment_u@pre && comment_v == comment_v@pre &&
                    comment_diff == comment_diff@pre &&
                    head == head@pre && nxt == nxt@pre && to == to@pre && wt == wt@pre &&
                    color == color@pre && stack_ == stack_@pre &&
                    1 <= n@pre && n@pre <= 200000 && 0 <= m@pre && m@pre <= 500000 &&
                    m@pre == Zlength(comments) &&
                    Zlength(comment_sources) == m@pre && Zlength(comment_targets) == m@pre &&
                    Zlength(comment_kinds) == m@pre &&
                    (forall q, (0 <= q && q < m@pre) =>
                      (1 <= comment_sources[q] && comment_sources[q] <= n@pre &&
                       1 <= comment_targets[q] && comment_targets[q] <= n@pre &&
                       comment_sources[q] != comment_targets[q] &&
                       (comment_kinds[q] == 0 || comment_kinds[q] == 1) &&
                       comment_sources[q] == fst(fst(comments[q])) &&
                       comment_targets[q] == snd(fst(comments[q])) &&
                       comment_kinds[q] == snd(comments[q]))) &&
                    1 <= s && s <= n@pre && 0 <= total && total <= n@pre &&
                    1 <= u && u <= n@pre &&
                    (cs[u] == 0 || cs[u] == 1) &&
                    0 <= top && top <= n@pre &&
                    0 <= c0 && 0 <= c1 && c0 + c1 <= n@pre &&
                    -1 <= e && e < 2 * m@pre &&
                    ((e != -1) =>
                      (1 <= ts[e] && ts[e] <= n@pre &&
                       (ws[e] == 0 || ws[e] == 1) &&
                       -1 <= ns[e] && ns[e] < 2 * m@pre)) &&
                    ((e != -1 && cs[ts[e]] < 0) => top < n@pre) &&
                    (forall j, (0 <= j && j < top) =>
                       (1 <= ks[j] && ks[j] <= n@pre)) &&
                    Zlength(before) == n@pre + 1 && Zlength(ks) == n@pre + 1 &&
                    ColourValues(n@pre, before) && ParityRespected(comments, before) &&
                    ColouredClosed(comments, before) &&
                    MaxImpostersOn(n@pre, comments, before, total) &&
                    (forall v0, (1 <= v0 && v0 < s) => before[v0] != -1) &&
                    before[s] == -1 &&
                    cs[s] != -1 &&
                    ComponentScanStrong(n@pre, comments, ns, before, cs, finished,
                                        sublist(0, top, ks), u, e, c0, c1) &&
                    ForwardStar(n@pre, m@pre, m@pre, hs, ns, ts, ws, comments) &&
                    ForwardStarRanges(n@pre, m@pre, hs, ns, ts, ws) &&
                    IntArray::full(comment_u@pre, m@pre, comment_sources) *
                    IntArray::full(comment_v@pre, m@pre, comment_targets) *
                    IntArray::full(comment_diff@pre, m@pre, comment_kinds) *
                    IntArray::full(head@pre, n@pre + 1, hs) *
                    IntArray::full(nxt@pre, 2 * m@pre, ns) *
                    IntArray::full(to@pre, 2 * m@pre, ts) *
                    IntArray::full(wt@pre, 2 * m@pre, ws) *
                    IntArray::full(color@pre, n@pre + 1, cs) *
                    IntArray::full(stack_@pre, n@pre + 1, ks)
            */
            for (int e = head[u]; e != -1; e = nxt[e]) {
                int v = to[e], want = color[u] ^ wt[e];
                if (color[v] < 0) {
                    color[v] = want;
                    { stack_[top] = v; top++; }
                } else if (color[v] != want) {
                    /*@ Assert
                          exists hs ns ts ws cs ks,
                            n == n@pre && m == m@pre &&
                            comment_u == comment_u@pre && comment_v == comment_v@pre &&
                            comment_diff == comment_diff@pre &&
                            head == head@pre && nxt == nxt@pre && to == to@pre && wt == wt@pre &&
                            color == color@pre && stack_ == stack_@pre &&
                            1 <= n@pre && n@pre <= 200000 &&
                            0 <= m@pre && m@pre <= 500000 &&
                            m@pre == Zlength(comments) &&
                            1 <= s && s <= n@pre && 0 <= total && total <= n@pre &&
                            0 <= top && top <= n@pre &&
                            0 <= c0 && 0 <= c1 && c0 + c1 <= n@pre &&
                            0 <= e && e < 2 * m@pre &&
                            1 <= u && u <= n@pre && 1 <= v && v <= n@pre &&
                            0 <= want && want <= 1 &&
                            Spec(n@pre, comments, -1) &&
                            IntArray::full(comment_u@pre, m@pre, comment_sources) *
                            IntArray::full(comment_v@pre, m@pre, comment_targets) *
                            IntArray::full(comment_diff@pre, m@pre, comment_kinds) *
                            IntArray::full(head@pre, n@pre + 1, hs) *
                            IntArray::full(nxt@pre, 2 * m@pre, ns) *
                            IntArray::full(to@pre, 2 * m@pre, ts) *
                            IntArray::full(wt@pre, 2 * m@pre, ws) *
                            IntArray::full(color@pre, n@pre + 1, cs) *
                            IntArray::full(stack_@pre, n@pre + 1, ks)
                    */
                    return -1;
                }
            }
        }
        /*@ Assert
              exists hs ns ts ws before cs ks vertices,
                n == n@pre && m == m@pre &&
                comment_u == comment_u@pre && comment_v == comment_v@pre &&
                comment_diff == comment_diff@pre &&
                head == head@pre && nxt == nxt@pre && to == to@pre && wt == wt@pre &&
                color == color@pre && stack_ == stack_@pre &&
                1 <= n@pre && n@pre <= 200000 && 0 <= m@pre && m@pre <= 500000 &&
                m@pre == Zlength(comments) &&
                Zlength(comment_sources) == m@pre && Zlength(comment_targets) == m@pre &&
                Zlength(comment_kinds) == m@pre &&
                (forall q, (0 <= q && q < m@pre) =>
                  (1 <= comment_sources[q] && comment_sources[q] <= n@pre &&
                   1 <= comment_targets[q] && comment_targets[q] <= n@pre &&
                   comment_sources[q] != comment_targets[q] &&
                   (comment_kinds[q] == 0 || comment_kinds[q] == 1) &&
                   comment_sources[q] == fst(fst(comments[q])) &&
                   comment_targets[q] == snd(fst(comments[q])) &&
                   comment_kinds[q] == snd(comments[q]))) &&
                1 <= s && s <= n@pre && 0 <= total && total <= n@pre &&
                top == 0 &&
                0 <= c0 && 0 <= c1 && c0 + c1 <= n@pre &&
                Zlength(before) == n@pre + 1 && Zlength(ks) == n@pre + 1 &&
                ColourValues(n@pre, before) && ParityRespected(comments, before) &&
                ColouredClosed(comments, before) &&
                MaxImpostersOn(n@pre, comments, before, total) &&
                (forall v0, (1 <= v0 && v0 < s) => before[v0] != -1) &&
                before[s] == -1 &&
                cs[s] != -1 &&
                ComponentCompleteStrong(n@pre, comments, before, cs, vertices, c0, c1) &&
                ForwardStar(n@pre, m@pre, m@pre, hs, ns, ts, ws, comments) &&
                ForwardStarRanges(n@pre, m@pre, hs, ns, ts, ws) &&
                IntArray::full(comment_u@pre, m@pre, comment_sources) *
                IntArray::full(comment_v@pre, m@pre, comment_targets) *
                IntArray::full(comment_diff@pre, m@pre, comment_kinds) *
                IntArray::full(head@pre, n@pre + 1, hs) *
                IntArray::full(nxt@pre, 2 * m@pre, ns) *
                IntArray::full(to@pre, 2 * m@pre, ts) *
                IntArray::full(wt@pre, 2 * m@pre, ws) *
                IntArray::full(color@pre, n@pre + 1, cs) *
                IntArray::full(stack_@pre, n@pre + 1, ks)
        */
        total += c0 > c1 ? c0 : c1;
    }
    /*@ Assert
          exists hs ns ts ws cs ks,
            n == n@pre && m == m@pre &&
            comment_u == comment_u@pre && comment_v == comment_v@pre &&
            comment_diff == comment_diff@pre &&
            head == head@pre && nxt == nxt@pre && to == to@pre && wt == wt@pre &&
            color == color@pre && stack_ == stack_@pre &&
            1 <= n@pre && n@pre <= 200000 && 0 <= m@pre && m@pre <= 500000 &&
            m@pre == Zlength(comments) && 0 <= total && total <= n@pre &&
            Spec(n@pre, comments, total) &&
            IntArray::full(comment_u@pre, m@pre, comment_sources) *
            IntArray::full(comment_v@pre, m@pre, comment_targets) *
            IntArray::full(comment_diff@pre, m@pre, comment_kinds) *
            IntArray::full(head@pre, n@pre + 1, hs) *
            IntArray::full(nxt@pre, 2 * m@pre, ns) *
            IntArray::full(to@pre, 2 * m@pre, ts) *
            IntArray::full(wt@pre, 2 * m@pre, ws) *
            IntArray::full(color@pre, n@pre + 1, cs) *
            IntArray::full(stack_@pre, n@pre + 1, ks)
    */
    return total;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         int n, m;
//         scanf("%d %d", &n, &m);
//         static int comment_u[MAXM], comment_v[MAXM], comment_diff[MAXM];
//         static int head[MAXN], nxt[2 * MAXM], to[2 * MAXM], wt[2 * MAXM];
//         static int color[MAXN], stack_[MAXN];
//         for (int q = 0; q < m; q++) {
//             int i, j;
//             char c[16];
//             scanf("%d %d %15s", &i, &j, c);
//             comment_u[q] = i;
//             comment_v[q] = j;
//             comment_diff[q] = (c[0] == 'i'); /* imposter: different roles */
//         }
//         printf("%lld\n", solver(n, m, comment_u, comment_v, comment_diff,
//                                 head, nxt, to, wt, color, stack_));
//     }
//     return 0;
// }
