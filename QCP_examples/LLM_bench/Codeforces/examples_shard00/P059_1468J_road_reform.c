/* Codeforces 1468/J - Road Reform */
// #include <stdio.h>
// #include <stdlib.h>
typedef struct
{
    int u, v;
    long long w;
} Edge;
/* QCP_INSERT_BEGIN:P059_1468J_road_reform.support */
/*@ Extern Coq
      (ztriple_1 : Z * Z * Z -> Z)
      (ztriple_2 : Z * Z * Z -> Z)
      (ztriple_3 : Z * Z * Z -> Z)
      (merge_int64_by_ints : Z -> Z -> Z -> Prop)
      (Pre : Z -> Z -> list (Z * Z * Z) -> Prop)
      (Spec : Z -> Z -> list (Z * Z * Z) -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P059_1468J_road_reform_lib */
/* QCP_INSERT_END:P059_1468J_road_reform.support */

/*@ Extern Coq
      (EdgeArray::full : Z -> Z -> list (Z * Z * Z) -> Assertion)
      (EdgeArray::missing_i : Z -> Z -> Z -> Z -> list (Z * Z * Z) -> Assertion)
      (EdgeArray::undef_full : Z -> Z -> Assertion)
      (EdgeArray::undef_missing_i : Z -> Z -> Z -> Z -> Assertion)
*/

/*@ Extern Coq
      (EdgeBlock : Z * Z * Z -> list Z -> Prop)
      (RoadCompareResult : Z * Z * Z -> Z * Z * Z -> Z -> Prop)
      (RoadEncoding : list (Z * Z * Z) -> list Z -> Prop)
      (RoadSortResult : list (Z * Z * Z) -> list (Z * Z * Z) -> list Z -> list Z -> Prop)
      (DSUState : Z -> list (Z * Z * Z) -> list Z -> list Z -> Prop)
      (DSUFindResult : Z -> list (Z * Z * Z) -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/

/*@ Extern Coq
      (FindProgress : Z -> list (Z * Z * Z) -> list Z -> Z -> Z -> list Z -> Prop)
      (ClosestRoadPrefix : Z -> list (Z * Z * Z) -> Z -> Z -> Prop)
      (KruskalPrefixState : Z -> Z -> list (Z * Z * Z) -> list (Z * Z * Z) -> list Z -> Z -> list Z -> Z -> Z -> Prop)
*/

/*@ Extern Coq
      (EdgeAllocationSize : Z -> Z -> Prop)
*/

/*@ Extern Coq
      (EdgeAllocationFits : Z -> Prop)
*/

/*@ Extern Coq
      (DSURootsPreserved : list Z -> list Z -> Prop)
*/

static int cmp_edge(const void *x, const void *y)
/*@ With (left right : Z * Z * Z)
    Require
      EdgeArray::full(x, 1, cons(left, nil)) *
      EdgeArray::full(y, 1, cons(right, nil))
    Ensure
      RoadCompareResult(left, right, __return) &&
      EdgeArray::full(x, 1, cons(left, nil)) *
      EdgeArray::full(y, 1, cons(right, nil))
*/
{
    /*@ Assert
        x == x@pre && y == y@pre &&
        data_at(&(((Edge *)x)->u), int, ztriple_1(left) - 1) *
        data_at(&(((Edge *)x)->v), int, ztriple_2(left) - 1) *
        data_at(&(((Edge *)x)->w), long long, ztriple_3(left)) *
        data_at(&(((Edge *)y)->u), int, ztriple_1(right) - 1) *
        data_at(&(((Edge *)y)->v), int, ztriple_2(right) - 1) *
        data_at(&(((Edge *)y)->w), long long, ztriple_3(right))
    */
    long long a = ((const Edge *)x)->w, b = ((const Edge *)y)->w;
    return (a > b) - (a < b);
}
static int find(int *p, int x)
/*@ With (n : Z) (roads : list (Z * Z * Z))
             (chosen parents : list Z)
    Require
      0 <= x && x < n && Zlength(parents) == n &&
      (forall i, (0 <= i && i < n) =>
        (0 <= parents[i] && parents[i] < n)) &&
      DSUState(n, roads, chosen, parents) &&
      IntArray::full(p, n, parents)
    Ensure
      exists parents_after,
        0 <= __return && __return < n &&
        Zlength(parents_after) == n &&
        (forall i, (0 <= i && i < n) =>
          (0 <= parents_after[i] && parents_after[i] < n)) &&
        DSURootsPreserved(parents, parents_after) &&
        DSUFindResult(n, roads, chosen, parents, parents_after,
                      x@pre, __return) &&
        IntArray::full(p, n, parents_after)
*/
{
    /*@ Inv Assert
        exists current_parents,
          p == p@pre &&
          0 <= x@pre && x@pre < n &&
          0 <= x && x < n &&
          Zlength(current_parents) == n &&
          (forall i, (0 <= i && i < n) =>
            (0 <= current_parents[i] && current_parents[i] < n)) &&
          DSUState(n, roads, chosen, parents) &&
          DSURootsPreserved(parents, current_parents) &&
          FindProgress(n, roads, chosen, x@pre, x, current_parents) &&
          IntArray::full(p, n, current_parents)
    */
    while (p[x] != x)
    {
        p[x] = p[p[x]];
        x = p[x];
    }
    return x;
}
typedef unsigned long size_t;

void *malloc(size_t size)
/*@ malloc_int
    With (cap : Z)
    Require
      0 <= cap && size == cap * sizeof(int)
    Ensure
      __return != 0 && IntArray::undef_full(__return, cap)
*/
/*@ malloc_edge
    With (cap : Z)
    Require
      0 <= cap && EdgeAllocationSize(size, cap)
    Ensure
      __return != 0 && EdgeArray::undef_full(__return, cap)
*/;

void qsort(Edge *base, size_t nmemb, size_t size,
           int (*compar)(const void *, const void *))
/*@ With (roads : list (Z * Z * Z))
    Require
      nmemb == Zlength(roads) && EdgeAllocationSize(size, 1) &&
      EdgeArray::full(base, nmemb, roads)
    Ensure
      exists sorted sorted_raw order,
        RoadSortResult(roads, sorted, sorted_raw, order) &&
        EdgeArray::full(base, nmemb, sorted)
*/;

void free(void *ptr)
/*@ free_int
    With (len cap : Z)
    Require
      0 <= len && len <= cap &&
      exists values,
        Zlength(values) == len &&
        IntArray::full(ptr, len, values) *
        IntArray::undef_seg(ptr, len, cap)
    Ensure emp
*/
/*@ free_edge
    With (cap : Z) (roads : list (Z * Z * Z))
    Require
      0 <= cap && Zlength(roads) == cap &&
      EdgeArray::full(ptr, cap, roads)
    Ensure emp
*/;
static long long solver(int n, int m, long long k,
                        const Edge *input) /* QCP_INSERT_BEGIN:P059_1468J_road_reform.contract */

/*@ With (roads : list (Z * Z * Z))
    Require
      2 <= n && n <= 200000 &&
      EdgeAllocationFits(m) &&
      1 <= k && k <= 1000000000 &&
      n - 1 <= Zlength(roads) &&
      (forall i, (0 <= i && i < Zlength(roads)) =>
        (1 <= ztriple_1(roads[i]) && ztriple_1(roads[i]) <= n &&
         1 <= ztriple_2(roads[i]) && ztriple_2(roads[i]) <= n &&
         1 <= ztriple_3(roads[i]) && ztriple_3(roads[i]) <= 1000000000)) &&
      Pre(n, k, roads) &&
      m == Zlength(roads) &&
      EdgeArray::full(input, m, roads)
    Ensure
      Spec(n, k, roads, __return) &&
      EdgeArray::full(input, m, roads)
*/
/* QCP_INSERT_END:P059_1468J_road_reform.contract */
{
    Edge *e = malloc((size_t)m * sizeof(*e))
        /*@ where (malloc_edge) cap = m */;
    long long closest = (1LL << 62);
    /*@ Inv Assert
        n == n@pre && m == m@pre && k == k@pre && input == input@pre &&
        2 <= n@pre && n@pre <= 200000 &&
        1 <= k@pre && k@pre <= 1000000000 &&
        Pre(n@pre, k@pre, roads) &&
        m@pre == Zlength(roads) && n@pre - 1 <= m@pre &&
        0 <= i && i <= m@pre &&
        0 <= closest &&
        ClosestRoadPrefix(k@pre, roads, i, closest) &&
        EdgeArray::full(input@pre, m@pre, roads) *
        EdgeArray::full(e, i, sublist(0, i, roads)) *
        EdgeArray::undef_full(e + i, m@pre - i)
    */
    for (int i = 0; i < m; ++i)
    {
        /*@ Assert
            n == n@pre && m == m@pre && k == k@pre && input == input@pre &&
            m@pre == Zlength(roads) && Pre(n@pre, k@pre, roads) &&
            0 <= i && i < m@pre &&
            ClosestRoadPrefix(k@pre, roads, i, closest) &&
            EdgeArray::missing_i(input@pre, i, 0, m@pre, roads) *
              data_at(&((input@pre + i)->u), int,
                      ztriple_1(roads[i]) - 1) *
              data_at(&((input@pre + i)->v), int,
                      ztriple_2(roads[i]) - 1) *
              data_at(&((input@pre + i)->w), long long,
                      ztriple_3(roads[i])) *
              EdgeArray::full(e, i, sublist(0, i, roads)) *
              undef_data_at(&((e + i)->u), int) *
              undef_data_at(&((e + i)->v), int) *
              undef_data_at(&((e + i)->w), long long) *
              EdgeArray::undef_full(e + i + 1, m@pre - i - 1)
        */
        e[i].u = input[i].u;
        e[i].v = input[i].v;
        e[i].w = input[i].w;
        long long d = e[i].w > k ? e[i].w - k : k - e[i].w;
        if (d < closest)
            closest = d;
    }
    /*@ Assert
        n == n@pre && m == m@pre && k == k@pre && input == input@pre &&
        2 <= n@pre && n@pre <= 200000 &&
        1 <= k@pre && k@pre <= 1000000000 &&
        Pre(n@pre, k@pre, roads) &&
        m@pre == Zlength(roads) && n@pre - 1 <= m@pre &&
        0 <= closest && closest <= 1000000000 &&
        ClosestRoadPrefix(k@pre, roads, m@pre, closest) &&
        EdgeArray::full(input@pre, m@pre, roads) *
        EdgeArray::full(e, m@pre, roads)
    */
    qsort(e, (size_t)m, sizeof(*e), cmp_edge)
        /*@ where roads = roads */;
    int *p = malloc((size_t)n * sizeof(*p))
        /*@ where (malloc_int) cap = n */;
    /*@ Inv Assert
        exists sorted_roads sorted_raw order initialized_parents,
          n == n@pre && m == m@pre && k == k@pre && input == input@pre &&
          2 <= n@pre && n@pre <= 200000 &&
          1 <= k@pre && k@pre <= 1000000000 &&
          Pre(n@pre, k@pre, roads) &&
          m@pre == Zlength(roads) && n@pre - 1 <= m@pre &&
          0 <= i && i <= n@pre &&
          0 <= closest && closest <= 1000000000 &&
          ClosestRoadPrefix(k@pre, roads, m@pre, closest) &&
          RoadSortResult(roads, sorted_roads, sorted_raw, order) &&
          Zlength(initialized_parents) == i &&
          (forall j, (0 <= j && j < i) => initialized_parents[j] == j) &&
          EdgeArray::full(input@pre, m@pre, roads) *
          EdgeArray::full(e, m@pre, sorted_roads) *
          IntArray::full(p, i, initialized_parents) *
          IntArray::undef_seg(p, i, n@pre)
    */
    for (int i = 0; i < n; ++i)
        p[i] = i;
    /*@ Assert
        exists sorted_roads sorted_raw order initialized_parents,
          n == n@pre && m == m@pre && k == k@pre && input == input@pre &&
          m@pre == Zlength(roads) &&
          2 <= n@pre && n@pre <= 200000 &&
          1 <= k@pre && k@pre <= 1000000000 &&
          Pre(n@pre, k@pre, roads) &&
          0 <= closest && closest <= 1000000000 &&
          ClosestRoadPrefix(k@pre, roads, m@pre, closest) &&
          RoadSortResult(roads, sorted_roads, sorted_raw, order) &&
          Zlength(initialized_parents) == n@pre &&
          (forall j, (0 <= j && j < n@pre) =>
            (initialized_parents[j] == j &&
             0 <= initialized_parents[j] && initialized_parents[j] < n@pre)) &&
          DSUState(n@pre, roads, nil, initialized_parents) &&
          EdgeArray::full(input@pre, m@pre, roads) *
          EdgeArray::full(e, m@pre, sorted_roads) *
          IntArray::full(p, n@pre, initialized_parents)
    */
    long long sum = 0;
    int used = 0;
    /*@ Inv Assert
        exists sorted_roads sorted_raw order parent selected,
          n == n@pre && m == m@pre && k == k@pre && input == input@pre &&
          2 <= n@pre && n@pre <= 200000 &&
          1 <= k@pre && k@pre <= 1000000000 &&
          Pre(n@pre, k@pre, roads) &&
          m@pre == Zlength(roads) && n@pre - 1 <= m@pre &&
          0 <= i && i <= m@pre &&
          0 <= used && used <= n@pre - 1 &&
          0 <= sum && sum <= 200000 * 1000000000 &&
          0 <= closest && closest <= 1000000000 &&
          Zlength(parent) == n@pre &&
          (forall j, (0 <= j && j < n@pre) =>
            (0 <= parent[j] && parent[j] < n@pre)) &&
          RoadSortResult(roads, sorted_roads, sorted_raw, order) &&
          ClosestRoadPrefix(k@pre, roads, m@pre, closest) &&
          DSUState(n@pre, roads, selected, parent) &&
          KruskalPrefixState(n@pre, k@pre, roads, sorted_roads, order,
                             i, selected, used, sum) &&
          EdgeArray::full(input@pre, m@pre, roads) *
          EdgeArray::full(e, m@pre, sorted_roads) *
          IntArray::full(p, n@pre, parent)
    */
    for (int i = 0; i < m && used < n - 1; ++i)
    {
        /*@ Given sorted_roads sorted_raw order parent selected */
        /*@ Assert
            n == n@pre && m == m@pre && k == k@pre && input == input@pre &&
            2 <= n@pre && n@pre <= 200000 &&
            1 <= k@pre && k@pre <= 1000000000 &&
            Pre(n@pre, k@pre, roads) &&
            m@pre == Zlength(roads) && n@pre - 1 <= m@pre &&
            0 <= i && i < m@pre &&
            0 <= used && used < n@pre - 1 &&
            0 <= sum && sum <= 200000 * 1000000000 &&
            0 <= closest && closest <= 1000000000 &&
            Zlength(parent) == n@pre &&
            (forall j, (0 <= j && j < n@pre) =>
              (0 <= parent[j] && parent[j] < n@pre)) &&
            RoadSortResult(roads, sorted_roads, sorted_raw, order) &&
            1 <= ztriple_1(sorted_roads[i]) &&
            ztriple_1(sorted_roads[i]) <= n@pre &&
            1 <= ztriple_2(sorted_roads[i]) &&
            ztriple_2(sorted_roads[i]) <= n@pre &&
            ClosestRoadPrefix(k@pre, roads, m@pre, closest) &&
            DSUState(n@pre, roads, selected, parent) &&
            KruskalPrefixState(n@pre, k@pre, roads, sorted_roads, order,
                               i, selected, used, sum) &&
            EdgeArray::full(input@pre, m@pre, roads) *
            EdgeArray::missing_i(e, i, 0, m@pre, sorted_roads) *
            data_at(&((e + i)->u), int,
                    ztriple_1(sorted_roads[i]) - 1) *
            data_at(&((e + i)->v), int,
                    ztriple_2(sorted_roads[i]) - 1) *
            data_at(&((e + i)->w), long long,
                    ztriple_3(sorted_roads[i])) *
            IntArray::full(p, n@pre, parent)
        */
        int a = find(p, e[i].u)
            /*@ where n = n, roads = roads, chosen = selected */;
        int b = find(p, e[i].v)
            /*@ where n = n, roads = roads, chosen = selected */;
        if (a != b)
        {
            p[a] = b;
            ++used;
            if (e[i].w > k)
                sum += e[i].w - k;
        }
    }
    /*@ Given sorted_roads sorted_raw order parent selected */
    /*@ Assert
        exists processed,
          n == n@pre && m == m@pre && k == k@pre && input == input@pre &&
          m@pre == Zlength(roads) &&
          Pre(n@pre, k@pre, roads) &&
          0 <= processed && processed <= m@pre && used == n@pre - 1 &&
          0 <= sum && sum <= 200000 * 1000000000 &&
          0 <= closest && closest <= 1000000000 &&
          Zlength(parent) == n@pre &&
          RoadSortResult(roads, sorted_roads, sorted_raw, order) &&
          RoadEncoding(sorted_roads, sorted_raw) &&
          ClosestRoadPrefix(k@pre, roads, m@pre, closest) &&
          DSUState(n@pre, roads, selected, parent) &&
          KruskalPrefixState(n@pre, k@pre, roads, sorted_roads, order,
                             processed, selected, used, sum) &&
          ((sum != 0 && Spec(n@pre, k@pre, roads, sum)) ||
           (sum == 0 && Spec(n@pre, k@pre, roads, closest))) &&
          EdgeArray::full(input@pre, m@pre, roads) *
          EdgeArray::full(e, m@pre, sorted_roads) *
          IntArray::full(p, n@pre, parent) *
          IntArray::undef_seg(p, n@pre, n@pre)
    */
    free(e) /*@ where (free_edge) cap = m, roads = sorted_roads */;
    free(p) /*@ where (free_int) len = n, cap = n */;
    return sum ? sum : closest;
}
// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//     while (t--)
//     {
//         int n, m;
//         long long k;
//         scanf("%d %d %lld", &n, &m, &k);
//         Edge *e = malloc((size_t)m * sizeof(*e));
//         for (int i = 0; i < m; ++i)
//         {
//             scanf("%d %d %lld", &e[i].u, &e[i].v, &e[i].w);
//             --e[i].u;
//             --e[i].v;
//         }
//         printf("%lld\n", solver(n, m, k, e));
//         free(e);
//     }
//     return 0;
// }
