/* Codeforces 1776/F - Train Splitting */
// #include <stdio.h>
// #include <stdlib.h>

typedef unsigned long size_t;

/* QCP_INSERT_BEGIN:P054_1776F_train_splitting.support */
/*@ Extern Coq
      (pair : {A} {B} -> A -> B -> A * B)
      (Pre : Z -> list (Z * Z) -> Prop)
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Spec : Z -> list (Z * Z) -> Z * list Z -> Prop)
      (DegreePrefix : Z -> list (Z * Z) -> Z -> list Z -> Prop)
      (PivotPrefix : Z -> list Z -> Z -> Prop)
      (PivotChoice : Z -> list Z -> Z -> Prop)
      (PivotColorPrefix : list (Z * Z) -> Z -> Z -> list Z -> Prop)
      (CompleteColorPrefix : list (Z * Z) -> Z -> Z -> list Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P054_1776F_train_splitting_lib */
/* QCP_INSERT_END:P054_1776F_train_splitting.support */

void *calloc(unsigned long nmemb, unsigned long size)
/*@ calloc_int
    With (cap : Z)
    Require
      0 <= cap &&
      nmemb == cap &&
      size == sizeof(int)
    Ensure
      __return != 0 &&
      IntArray::full(__return, cap, repeat_Z(0, cap))
*/;

void free(void *ptr)
/*@ free_int
    Require exists values cap,
      IntArray::full(ptr, cap, values)
    Ensure emp
*/;

static int solver(int n, int m, const int *u, const int *v, int *colors)
/* QCP_INSERT_BEGIN:P054_1776F_train_splitting.contract */

/*@ With (e : list (Z * Z))
             (u_data v_data : list Z)
    Require
      3 <= n && n <= 50 &&
      n - 1 <= Zlength(e) && Zlength(e) <= 1225 &&
      (forall i, (0 <= i && i < Zlength(e)) =>
        ((0 <= fst(e[i]) && fst(e[i]) < n) &&
         (0 <= snd(e[i]) && snd(e[i]) < n))) &&
      Pre(n, e) &&
      m == Zlength(e) && Zlength(u_data) == m && Zlength(v_data) == m &&
      (forall i, (0 <= i && i < m) =>
        (u_data[i] == fst(e[i]) && v_data[i] == snd(e[i]))) &&
      IntArray::full(u, m, u_data) * IntArray::full(v, m, v_data) *
      IntArray::undef_full(colors, m)
    Ensure
      exists color_count result,
        Spec(n, e, pair(color_count, result)) && __return == color_count &&
        IntArray::full(u, m, u_data) * IntArray::full(v, m, v_data) *
        IntArray::full(colors, m, result)
*/
/* QCP_INSERT_END:P054_1776F_train_splitting.contract */

{
    int *deg = calloc((size_t)n, sizeof(*deg))
      /*@ where (calloc_int) cap = n */;

    /*@ Inv Assert
          exists degrees,
            n == n@pre && m == m@pre && u == u@pre && v == v@pre &&
            colors == colors@pre && deg != 0 &&
            3 <= n@pre && n@pre <= 50 &&
            n@pre - 1 <= m@pre && m@pre <= 1225 &&
            m@pre == Zlength(e) &&
            Zlength(u_data) == m@pre && Zlength(v_data) == m@pre &&
            (forall k, (0 <= k && k < m@pre) =>
              ((0 <= u_data[k] && u_data[k] < n@pre) &&
               (0 <= v_data[k] && v_data[k] < n@pre) &&
               u_data[k] == fst(e[k]) && v_data[k] == snd(e[k]))) &&
            Pre(n@pre, e) && 0 <= i && i <= m@pre &&
            DegreePrefix(n@pre, e, i, degrees) &&
            (forall x, (0 <= x && x < n@pre) =>
              (0 <= degrees[x] && degrees[x] <= 2 * i)) &&
            IntArray::full(u@pre, m@pre, u_data) *
            IntArray::full(v@pre, m@pre, v_data) *
            IntArray::undef_full(colors@pre, m@pre) *
            IntArray::full(deg, n@pre, degrees)
    */
    for (int i = 0; i < m; ++i) {
        ++deg[u[i]];
        ++deg[v[i]];
    }

    int pivot = -1;
    /*@ Inv Assert
          exists degrees,
            n == n@pre && m == m@pre && u == u@pre && v == v@pre &&
            colors == colors@pre && deg != 0 && pivot == -1 &&
            3 <= n@pre && n@pre <= 50 &&
            n@pre - 1 <= m@pre && m@pre <= 1225 &&
            m@pre == Zlength(e) &&
            Zlength(u_data) == m@pre && Zlength(v_data) == m@pre &&
            (forall k, (0 <= k && k < m@pre) =>
              ((0 <= u_data[k] && u_data[k] < n@pre) &&
               (0 <= v_data[k] && v_data[k] < n@pre) &&
               u_data[k] == fst(e[k]) && v_data[k] == snd(e[k]))) &&
            Pre(n@pre, e) && 0 <= i && i <= n@pre &&
            DegreePrefix(n@pre, e, m@pre, degrees) &&
            PivotPrefix(n@pre, degrees, i) &&
            (forall x, (0 <= x && x < n@pre) =>
              (0 <= degrees[x] && degrees[x] <= n@pre - 1)) &&
            IntArray::full(u@pre, m@pre, u_data) *
            IntArray::full(v@pre, m@pre, v_data) *
            IntArray::undef_full(colors@pre, m@pre) *
            IntArray::full(deg, n@pre, degrees)
    */
    for (int i = 0; i < n; ++i) {
        if (deg[i] < n - 1) {
            pivot = i;
            break;
        }
    }

    /*@ Assert
          exists degrees,
            n == n@pre && m == m@pre && u == u@pre && v == v@pre &&
            colors == colors@pre && deg != 0 &&
            3 <= n@pre && n@pre <= 50 &&
            n@pre - 1 <= m@pre && m@pre <= 1225 &&
            m@pre == Zlength(e) &&
            Zlength(u_data) == m@pre && Zlength(v_data) == m@pre &&
            (forall k, (0 <= k && k < m@pre) =>
              ((0 <= u_data[k] && u_data[k] < n@pre) &&
               (0 <= v_data[k] && v_data[k] < n@pre) &&
               u_data[k] == fst(e[k]) && v_data[k] == snd(e[k]))) &&
            Pre(n@pre, e) &&
            DegreePrefix(n@pre, e, m@pre, degrees) &&
            PivotChoice(n@pre, degrees, pivot) &&
            IntArray::full(u@pre, m@pre, u_data) *
            IntArray::full(v@pre, m@pre, v_data) *
            IntArray::undef_full(colors@pre, m@pre) *
            IntArray::full(deg, n@pre, degrees)
    */

    int kinds;
    if (pivot >= 0) {
        kinds = 2;
        /*@ Inv Assert
              exists degrees labels,
                n == n@pre && m == m@pre && u == u@pre && v == v@pre &&
                colors == colors@pre && deg != 0 && kinds == 2 &&
                0 <= pivot && pivot < n@pre &&
                3 <= n@pre && n@pre <= 50 &&
                n@pre - 1 <= m@pre && m@pre <= 1225 &&
                m@pre == Zlength(e) &&
                Zlength(u_data) == m@pre && Zlength(v_data) == m@pre &&
                (forall k, (0 <= k && k < m@pre) =>
                  ((0 <= u_data[k] && u_data[k] < n@pre) &&
                   (0 <= v_data[k] && v_data[k] < n@pre) &&
                   u_data[k] == fst(e[k]) && v_data[k] == snd(e[k]))) &&
                Pre(n@pre, e) &&
                DegreePrefix(n@pre, e, m@pre, degrees) &&
                PivotChoice(n@pre, degrees, pivot) &&
                0 <= i && i <= m@pre &&
                PivotColorPrefix(e, pivot, i, labels) &&
                IntArray::full(u@pre, m@pre, u_data) *
                IntArray::full(v@pre, m@pre, v_data) *
                IntArray::seg(colors@pre, 0, i, labels) *
                IntArray::undef_seg(colors@pre, i, m@pre) *
                IntArray::full(deg, n@pre, degrees)
        */
        for (int i = 0; i < m; ++i) {
            colors[i] = (u[i] == pivot || v[i] == pivot) ? 1 : 2;
        }
    } else {
        kinds = 3;
        int first = 1;
        /*@ Inv Assert
              exists degrees labels,
                n == n@pre && m == m@pre && u == u@pre && v == v@pre &&
                colors == colors@pre && deg != 0 && kinds == 3 && pivot == -1 &&
                3 <= n@pre && n@pre <= 50 &&
                n@pre - 1 <= m@pre && m@pre <= 1225 &&
                m@pre == Zlength(e) &&
                Zlength(u_data) == m@pre && Zlength(v_data) == m@pre &&
                (forall k, (0 <= k && k < m@pre) =>
                  ((0 <= u_data[k] && u_data[k] < n@pre) &&
                   (0 <= v_data[k] && v_data[k] < n@pre) &&
                   u_data[k] == fst(e[k]) && v_data[k] == snd(e[k]))) &&
                Pre(n@pre, e) &&
                DegreePrefix(n@pre, e, m@pre, degrees) &&
                PivotChoice(n@pre, degrees, pivot) &&
                0 <= i && i <= m@pre &&
                (first == 0 || first == 1) &&
                CompleteColorPrefix(e, i, first, labels) &&
                IntArray::full(u@pre, m@pre, u_data) *
                IntArray::full(v@pre, m@pre, v_data) *
                IntArray::seg(colors@pre, 0, i, labels) *
                IntArray::undef_seg(colors@pre, i, m@pre) *
                IntArray::full(deg, n@pre, degrees)
        */
        for (int i = 0; i < m; ++i) {
            if (u[i] == 0 || v[i] == 0) {
                colors[i] = first ? 1 : 2;
                first = 0;
            } else {
                colors[i] = 3;
            }
        }
    }

    /*@ Assert
          exists degrees result,
            n == n@pre && m == m@pre && u == u@pre && v == v@pre &&
            colors == colors@pre && deg != 0 &&
            3 <= n@pre && n@pre <= 50 &&
            ((0 <= pivot && pivot < n@pre && kinds == 2) ||
             (pivot == -1 && kinds == 3)) &&
            m@pre == Zlength(e) &&
            Zlength(u_data) == m@pre && Zlength(v_data) == m@pre &&
            Pre(n@pre, e) &&
            Zlength(result) == m@pre &&
            Spec(n@pre, e, pair(kinds, result)) &&
            IntArray::full(u@pre, m@pre, u_data) *
            IntArray::full(v@pre, m@pre, v_data) *
            IntArray::full(colors@pre, m@pre, result) *
            IntArray::full(deg, n@pre, degrees)
    */
    free(deg) /*@ where (free_int) */;
    return kinds;
}

// int main(void)
// {
//     int t;scanf("%d",&t);while(t--){int n,m;scanf("%d %d",&n,&m);int *u=malloc((size_t)m*sizeof(*u)),*v=malloc((size_t)m*sizeof(*v)),*colors=malloc((size_t)m*sizeof(*colors));
//         for(int i=0;i<m;++i){scanf("%d %d",&u[i],&v[i]);--u[i];--v[i];}
//         printf("%d\n",solver(n,m,u,v,colors));for(int i=0;i<m;++i)printf("%d%c",colors[i],i+1==m?'\n':' ');
//         free(colors);free(u);free(v);
//     }return 0;
// }
