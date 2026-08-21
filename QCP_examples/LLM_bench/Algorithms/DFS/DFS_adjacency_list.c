#include "safeexec_def.h"
#include "int_array_def.h"
#include "sll_def.h"

/*@ Import Coq Require Import Algorithms.DFS.DFS */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.DFS.DFS_adjacency_list_lib */
/*@ Import Coq Import ZSimpleGraph */

/*@ Extern Coq (G :: *) */
/*@ Extern Coq
      (DFSAdjacencyList::dfs_program :
        G -> Z -> program (Z -> Prop) unit)
      (DFSAdjacencyList::dfs_loop :
        G -> Z -> program (Z -> Prop) unit)
      (DFSAdjacencyList::dfs_continue :
        G -> Z -> unit -> program (Z -> Prop) unit)
      (eq : {A} -> A -> A -> Prop)
      (DFSAdjacencyList::is_reachable : G -> Z -> Z -> Prop)
      (DFSAdjacencyList::all_visited :
        list Z -> (Z -> Prop) -> Prop)
      (DFSAdjacencyList::visited_extension :
        (Z -> Prop) -> (Z -> Prop) -> Prop)
      (DFSAdjacencyList::empty_visited :
        (Z -> Prop) -> Prop)
      (ZSimpleGraph::vertex_count : G -> Z)
      (ZSimpleGraph::vertex_valid : G -> Z -> Prop)
      (ZSimpleGraph::visited_values :
        G -> list Z -> (Z -> Prop) -> Prop)
      (DFSAdjacencyList::graph_rep :
        Z -> G -> list Z -> list (list Z) -> list (list Z) -> Assertion)
      (DFSAdjacencyList::graph_except :
        Z -> G -> list Z -> list (list Z) -> list (list Z) -> Z -> Assertion)
      (DFSAdjacencyList::addressed_sll :
        Z -> list Z -> list Z -> Assertion)
      (DFSAdjacencyList::addressed_sllseg :
        Z -> Z -> list Z -> list Z -> Assertion)
      (DFSAdjacencyList::graph : Z -> G -> Assertion)
      (DFSAdjacencyList::visited : Z -> G -> (Z -> Prop) -> Assertion)
 */

/*
 * Recursive depth-first search over a linked-list adjacency graph.
 *
 * Vertices are numbered from 0 through vertex_count - 1.  For every vertex
 * u, adjacency[u] is the head of a linked list whose data fields contain u's
 * neighbor vertex numbers.  The graph storage is read-only; visited is
 * supplied by the caller and is updated in place.
 */
void dfs_adjacency_list(struct list **adjacency, int vertex_count,
                        int *visited, int vertex)
/*@ high_level_spec <= low_level_spec
    With (g: G) (initial_visited_set: Z -> Prop)
    Require
      vertex_count == ZSimpleGraph::vertex_count(g) &&
      0 < vertex_count && vertex_count < INT_MAX &&
      ZSimpleGraph::vertex_valid(g, vertex) &&
      DFSAdjacencyList::empty_visited(initial_visited_set) &&
      DFSAdjacencyList::graph(adjacency, g) *
      DFSAdjacencyList::visited(visited, g, initial_visited_set)
    Ensure
      exists (high_visited_set: Z -> Prop),
        (forall (v: Z),
          high_visited_set(v) => DFSAdjacencyList::is_reachable(g, vertex, v)) &&
        (forall (v: Z),
          DFSAdjacencyList::is_reachable(g, vertex, v) => high_visited_set(v)) &&
        DFSAdjacencyList::graph(adjacency, g) *
        DFSAdjacencyList::visited(visited, g, high_visited_set)
 */
;

void dfs_adjacency_list(struct list **adjacency, int vertex_count,
                        int *visited, int vertex)
/*@ bind_spec <= low_level_spec
    With {B} (g: G) (row_ptrs: list Z)
         (node_addrs: list (list Z)) (rows: list (list Z))
         (visited_set: Z -> Prop)
         (c: unit -> program (Z -> Prop) B) X
    Require
      vertex_count == ZSimpleGraph::vertex_count(g) &&
      0 < vertex_count && vertex_count < INT_MAX &&
      ZSimpleGraph::vertex_valid(g, vertex) &&
      safeExec(eq(visited_set),
        bind(DFSAdjacencyList::dfs_program(g, vertex), c), X) &&
      DFSAdjacencyList::graph_rep(
        adjacency, g, row_ptrs, node_addrs, rows) *
      DFSAdjacencyList::visited(visited, g, visited_set)
    Ensure
      exists (bind_visited_set: Z -> Prop),
        DFSAdjacencyList::visited_extension(
          visited_set, bind_visited_set) &&
        bind_visited_set(vertex) &&
        safeExec(eq(bind_visited_set), applyf(c, tt), X) &&
        DFSAdjacencyList::graph_rep(
          adjacency, g, row_ptrs, node_addrs, rows) *
        DFSAdjacencyList::visited(visited, g, bind_visited_set)
 */
;

void dfs_adjacency_list(struct list **adjacency, int vertex_count,
                        int *visited, int vertex)
/*@ low_level_spec
    With (g: G) (row_ptrs: list Z)
         (node_addrs: list (list Z)) (rows: list (list Z))
         (visited_set: Z -> Prop) X
    Require
      vertex_count == ZSimpleGraph::vertex_count(g) &&
      0 < vertex_count && vertex_count < INT_MAX &&
      ZSimpleGraph::vertex_valid(g, vertex) &&
      safeExec(eq(visited_set),
        DFSAdjacencyList::dfs_program(g, vertex), X) &&
      DFSAdjacencyList::graph_rep(
        adjacency, g, row_ptrs, node_addrs, rows) *
      DFSAdjacencyList::visited(visited, g, visited_set)
    Ensure
      exists (low_visited_set: Z -> Prop),
        DFSAdjacencyList::visited_extension(
          visited_set, low_visited_set) &&
        low_visited_set(vertex) &&
        safeExec(eq(low_visited_set), return(tt), X) &&
        DFSAdjacencyList::graph_rep(
          adjacency, g, row_ptrs, node_addrs, rows) *
        DFSAdjacencyList::visited(visited, g, low_visited_set)
 */
{
    /*@ Assert
          exists (values: list Z),
            adjacency == adjacency@pre &&
            vertex_count == vertex_count@pre &&
            visited == visited@pre && vertex == vertex@pre &&
            vertex_count == ZSimpleGraph::vertex_count(g) &&
            0 < vertex_count && vertex_count < INT_MAX &&
            ZSimpleGraph::vertex_valid(g, vertex) &&
            0 <= vertex && vertex < vertex_count &&
            safeExec(eq(visited_set),
              DFSAdjacencyList::dfs_program(g, vertex), X) &&
            ZSimpleGraph::visited_values(g, values, visited_set) &&
            DFSAdjacencyList::graph_rep(
              adjacency, g, row_ptrs, node_addrs, rows) *
            IntArray::full(visited, vertex_count, values)
     */
    visited[vertex] = 1;

    /*@ Assert
          exists (entered_set: Z -> Prop) (entered_values: list Z),
            adjacency == adjacency@pre &&
            vertex_count == vertex_count@pre &&
            visited == visited@pre && vertex == vertex@pre &&
            vertex_count == ZSimpleGraph::vertex_count(g) &&
            0 < vertex_count && vertex_count < INT_MAX &&
            ZSimpleGraph::vertex_valid(g, vertex) &&
            0 <= vertex && vertex < vertex_count &&
            DFSAdjacencyList::visited_extension(
              visited_set, entered_set) &&
            entered_set(vertex) &&
            safeExec(eq(entered_set),
              DFSAdjacencyList::dfs_loop(g, vertex), X) &&
            ZSimpleGraph::visited_values(g, entered_values, entered_set) &&
            DFSAdjacencyList::graph_rep(
              adjacency, g, row_ptrs, node_addrs, rows) *
            IntArray::full(visited, vertex_count, entered_values)
     */

    /*@ Assert
          exists (split_set: Z -> Prop) (split_values: list Z)
                 (row_head: Z) (row row_node_addrs: list Z),
            adjacency == adjacency@pre &&
            vertex_count == vertex_count@pre &&
            visited == visited@pre && vertex == vertex@pre &&
            vertex_count == ZSimpleGraph::vertex_count(g) &&
            0 < vertex_count && vertex_count < INT_MAX &&
            ZSimpleGraph::vertex_valid(g, vertex) &&
            0 <= vertex && vertex < vertex_count &&
            row_head == Znth(vertex, row_ptrs, 0) &&
            row_node_addrs == Znth(vertex, node_addrs, nil) &&
            row == Znth(vertex, rows, nil) &&
            DFSAdjacencyList::visited_extension(
              visited_set, split_set) &&
            split_set(vertex) &&
            safeExec(eq(split_set),
              DFSAdjacencyList::dfs_loop(g, vertex), X) &&
            ZSimpleGraph::visited_values(g, split_values, split_set) &&
            store(adjacency + vertex * sizeof(struct list *),
              struct list *, row_head) *
            DFSAdjacencyList::graph_except(
              adjacency, g, row_ptrs, node_addrs, rows, vertex) *
            DFSAdjacencyList::addressed_sll(
              row_head, row_node_addrs, row) *
            IntArray::full(visited, vertex_count, split_values)
     */
    struct list *edge = adjacency[vertex];

    /*@ Inv Assert
          exists (loop_set: Z -> Prop) (loop_values: list Z)
                 (edge_value row_head: Z)
                 (row row_node_addrs done_addrs todo_addrs: list Z)
                 (done todo: list Z),
            adjacency == adjacency@pre &&
            vertex_count == vertex_count@pre &&
            visited == visited@pre && vertex == vertex@pre &&
            vertex_count == ZSimpleGraph::vertex_count(g) &&
            0 < vertex_count && vertex_count < INT_MAX &&
            ZSimpleGraph::vertex_valid(g, vertex) &&
            0 <= vertex && vertex < vertex_count &&
            row_head == Znth(vertex, row_ptrs, 0) &&
            row_node_addrs == Znth(vertex, node_addrs, nil) &&
            row == Znth(vertex, rows, nil) &&
            row_node_addrs == app(done_addrs, todo_addrs) &&
            row == app(done, todo) &&
            Zlength(done_addrs) == Zlength(done) &&
            DFSAdjacencyList::visited_extension(
              visited_set, loop_set) &&
            loop_set(vertex) &&
            DFSAdjacencyList::all_visited(done, loop_set) &&
            safeExec(eq(loop_set),
              DFSAdjacencyList::dfs_loop(g, vertex), X) &&
            ZSimpleGraph::visited_values(g, loop_values, loop_set) &&
            edge == edge_value &&
            store(adjacency + vertex * sizeof(struct list *),
              struct list *, row_head) *
            DFSAdjacencyList::graph_except(
              adjacency, g, row_ptrs, node_addrs, rows, vertex) *
            DFSAdjacencyList::addressed_sllseg(
              row_head, edge_value, done_addrs, done) *
            DFSAdjacencyList::addressed_sll(
              edge_value, todo_addrs, todo) *
            IntArray::full(visited, vertex_count, loop_values)
     */
    while (edge != (struct list *)0) {
        /*@ Assert
              exists (cursor_set: Z -> Prop) (cursor_values: list Z)
                     (edge_value row_head next datum: Z)
                     (row row_node_addrs done_addrs rest_addrs: list Z)
                     (done rest: list Z),
                adjacency == adjacency@pre &&
                vertex_count == vertex_count@pre &&
                visited == visited@pre && vertex == vertex@pre &&
                vertex_count == ZSimpleGraph::vertex_count(g) &&
                0 < vertex_count && vertex_count < INT_MAX &&
                ZSimpleGraph::vertex_valid(g, vertex) &&
                ZSimpleGraph::vertex_valid(g, datum) &&
                0 <= vertex && vertex < vertex_count &&
                0 <= datum && datum < vertex_count &&
                edge_value != 0 &&
                row_head == Znth(vertex, row_ptrs, 0) &&
                row_node_addrs == Znth(vertex, node_addrs, nil) &&
                row == Znth(vertex, rows, nil) &&
                row_node_addrs ==
                  app(done_addrs, cons(edge_value, rest_addrs)) &&
                row == app(done, cons(datum, rest)) &&
                Zlength(done_addrs) == Zlength(done) &&
                DFSAdjacencyList::visited_extension(
                  visited_set, cursor_set) &&
                cursor_set(vertex) &&
                DFSAdjacencyList::all_visited(done, cursor_set) &&
                safeExec(eq(cursor_set),
                  DFSAdjacencyList::dfs_loop(g, vertex), X) &&
                ZSimpleGraph::visited_values(
                  g, cursor_values, cursor_set) &&
                edge == edge_value &&
                store(adjacency + vertex * sizeof(struct list *),
                  struct list *, row_head) *
                DFSAdjacencyList::graph_except(
                  adjacency, g, row_ptrs, node_addrs, rows, vertex) *
                DFSAdjacencyList::addressed_sllseg(
                  row_head, edge_value, done_addrs, done) *
                store(&(edge_value->data), int, datum) *
                store(&(edge_value->next), struct list *, next) *
                DFSAdjacencyList::addressed_sll(
                  next, rest_addrs, rest) *
                IntArray::full(visited, vertex_count, cursor_values)
         */
        int neighbor = edge->data;

            /*@ Assert
              exists (read_set: Z -> Prop) (read_values: list Z)
                     (edge_value row_head next: Z)
                     (row row_node_addrs done_addrs rest_addrs: list Z)
                     (done rest: list Z),
                adjacency == adjacency@pre &&
                vertex_count == vertex_count@pre &&
                visited == visited@pre && vertex == vertex@pre &&
                vertex_count == ZSimpleGraph::vertex_count(g) &&
                0 < vertex_count && vertex_count < INT_MAX &&
                ZSimpleGraph::vertex_valid(g, vertex) &&
                ZSimpleGraph::vertex_valid(g, neighbor) &&
                0 <= vertex && vertex < vertex_count &&
                0 <= neighbor && neighbor < vertex_count &&
                edge_value != 0 &&
                row_head == Znth(vertex, row_ptrs, 0) &&
                row_node_addrs == Znth(vertex, node_addrs, nil) &&
                row == Znth(vertex, rows, nil) &&
                row_node_addrs ==
                  app(done_addrs, cons(edge_value, rest_addrs)) &&
                row == app(done, cons(neighbor, rest)) &&
                Zlength(done_addrs) == Zlength(done) &&
                DFSAdjacencyList::visited_extension(
                  visited_set, read_set) &&
                read_set(vertex) &&
                DFSAdjacencyList::all_visited(done, read_set) &&
                safeExec(eq(read_set),
                  DFSAdjacencyList::dfs_loop(g, vertex), X) &&
                ZSimpleGraph::visited_values(g, read_values, read_set) &&
                edge == edge_value &&
                store(adjacency + vertex * sizeof(struct list *),
                  struct list *, row_head) *
                DFSAdjacencyList::graph_except(
                  adjacency, g, row_ptrs, node_addrs, rows, vertex) *
                DFSAdjacencyList::addressed_sllseg(
                  row_head, edge_value, done_addrs, done) *
                store(&(edge_value->data), int, neighbor) *
                store(&(edge_value->next), struct list *, next) *
                DFSAdjacencyList::addressed_sll(
                  next, rest_addrs, rest) *
                store(visited + neighbor * sizeof(int), int,
                  Znth(neighbor, read_values, 0)) *
                IntArray::missing_i(
                  visited, neighbor, 0, vertex_count, read_values)
         */
        if (visited[neighbor] == 0) {
            /*@ Assert
                  exists (call_set: Z -> Prop)
                         (edge_value row_head next: Z)
                         (row row_node_addrs done_addrs rest_addrs: list Z)
                         (done rest: list Z),
                    adjacency == adjacency@pre &&
                    vertex_count == vertex_count@pre &&
                    visited == visited@pre && vertex == vertex@pre &&
                    vertex_count == ZSimpleGraph::vertex_count(g) &&
                    0 < vertex_count && vertex_count < INT_MAX &&
                    ZSimpleGraph::vertex_valid(g, vertex) &&
                    ZSimpleGraph::vertex_valid(g, neighbor) &&
                    0 <= vertex && vertex < vertex_count &&
                    0 <= neighbor && neighbor < vertex_count &&
                    edge_value != 0 &&
                    row_head == Znth(vertex, row_ptrs, 0) &&
                    row_node_addrs == Znth(vertex, node_addrs, nil) &&
                    row == Znth(vertex, rows, nil) &&
                    row_node_addrs ==
                      app(done_addrs, cons(edge_value, rest_addrs)) &&
                    row == app(done, cons(neighbor, rest)) &&
                    Zlength(done_addrs) == Zlength(done) &&
                    DFSAdjacencyList::visited_extension(
                      visited_set, call_set) &&
                    call_set(vertex) &&
                    DFSAdjacencyList::all_visited(done, call_set) &&
                    safeExec(eq(call_set),
                      bind(DFSAdjacencyList::dfs_program(g, neighbor),
                        DFSAdjacencyList::dfs_continue(g, vertex)), X) &&
                    edge == edge_value &&
                    DFSAdjacencyList::graph_rep(
                      adjacency, g, row_ptrs, node_addrs, rows) *
                    DFSAdjacencyList::visited(
                      visited, g, call_set)
             */
            /*@ Given call_set */
            dfs_adjacency_list(adjacency, vertex_count, visited, neighbor)
              /*@ where(bind_spec)
                    g = g, row_ptrs = row_ptrs,
                    node_addrs = node_addrs, rows = rows,
                    visited_set = call_set,
                    c = DFSAdjacencyList::dfs_continue(g, vertex), X = X;
                    B = unit */;

            /*@ Assert
                  exists (after_set: Z -> Prop) (after_values: list Z)
                         (edge_value row_head next: Z)
                         (row row_node_addrs done_addrs rest_addrs: list Z)
                         (done rest: list Z),
                    adjacency == adjacency@pre &&
                    vertex_count == vertex_count@pre &&
                    visited == visited@pre && vertex == vertex@pre &&
                    vertex_count == ZSimpleGraph::vertex_count(g) &&
                    0 < vertex_count && vertex_count < INT_MAX &&
                    ZSimpleGraph::vertex_valid(g, vertex) &&
                    ZSimpleGraph::vertex_valid(g, neighbor) &&
                    0 <= vertex && vertex < vertex_count &&
                    0 <= neighbor && neighbor < vertex_count &&
                    edge_value != 0 &&
                    row_head == Znth(vertex, row_ptrs, 0) &&
                    row_node_addrs == Znth(vertex, node_addrs, nil) &&
                    row == Znth(vertex, rows, nil) &&
                    row_node_addrs ==
                      app(done_addrs, cons(edge_value, rest_addrs)) &&
                    row == app(done, cons(neighbor, rest)) &&
                    Zlength(done_addrs) == Zlength(done) &&
                    DFSAdjacencyList::visited_extension(
                      visited_set, after_set) &&
                    after_set(vertex) &&
                    DFSAdjacencyList::all_visited(
                      app(done, cons(neighbor, nil)), after_set) &&
                    safeExec(eq(after_set),
                      DFSAdjacencyList::dfs_loop(g, vertex), X) &&
                    ZSimpleGraph::visited_values(
                      g, after_values, after_set) &&
                    edge == edge_value &&
                    store(adjacency + vertex * sizeof(struct list *),
                      struct list *, row_head) *
                    DFSAdjacencyList::graph_except(
                      adjacency, g, row_ptrs, node_addrs, rows, vertex) *
                    DFSAdjacencyList::addressed_sllseg(
                      row_head, edge_value, done_addrs, done) *
                    store(&(edge_value->data), int, neighbor) *
                    store(&(edge_value->next), struct list *, next) *
                    DFSAdjacencyList::addressed_sll(
                      next, rest_addrs, rest) *
                    IntArray::full(
                      visited, vertex_count, after_values)
             */
        } else {
        }

        /*@ Assert
              exists (next_set: Z -> Prop) (next_values: list Z)
                     (edge_value row_head next: Z)
                     (row row_node_addrs done_addrs rest_addrs: list Z)
                     (done rest: list Z),
                adjacency == adjacency@pre &&
                vertex_count == vertex_count@pre &&
                visited == visited@pre && vertex == vertex@pre &&
                vertex_count == ZSimpleGraph::vertex_count(g) &&
                0 < vertex_count && vertex_count < INT_MAX &&
                ZSimpleGraph::vertex_valid(g, vertex) &&
                ZSimpleGraph::vertex_valid(g, neighbor) &&
                0 <= vertex && vertex < vertex_count &&
                0 <= neighbor && neighbor < vertex_count &&
                edge_value != 0 &&
                row_head == Znth(vertex, row_ptrs, 0) &&
                row_node_addrs == Znth(vertex, node_addrs, nil) &&
                row == Znth(vertex, rows, nil) &&
                row_node_addrs ==
                  app(done_addrs, cons(edge_value, rest_addrs)) &&
                row == app(done, cons(neighbor, rest)) &&
                Zlength(done_addrs) == Zlength(done) &&
                DFSAdjacencyList::visited_extension(
                  visited_set, next_set) &&
                next_set(vertex) &&
                DFSAdjacencyList::all_visited(
                  app(done, cons(neighbor, nil)), next_set) &&
                safeExec(eq(next_set),
                  DFSAdjacencyList::dfs_loop(g, vertex), X) &&
                ZSimpleGraph::visited_values(g, next_values, next_set) &&
                edge == edge_value &&
                store(adjacency + vertex * sizeof(struct list *),
                  struct list *, row_head) *
                DFSAdjacencyList::graph_except(
                  adjacency, g, row_ptrs, node_addrs, rows, vertex) *
                DFSAdjacencyList::addressed_sllseg(
                  row_head, edge_value, done_addrs, done) *
                store(&(edge_value->data), int, neighbor) *
                store(&(edge_value->next), struct list *, next) *
                DFSAdjacencyList::addressed_sll(
                  next, rest_addrs, rest) *
                IntArray::full(visited, vertex_count, next_values)
         */
        edge = edge->next;

    }

    /*@ Assert
          exists (visited_set_out: Z -> Prop),
            adjacency == adjacency@pre &&
            vertex_count == vertex_count@pre &&
            visited == visited@pre && vertex == vertex@pre &&
            DFSAdjacencyList::visited_extension(
              visited_set, visited_set_out) &&
            visited_set_out(vertex@pre) &&
            safeExec(eq(visited_set_out), return(tt), X) &&
            edge == 0 &&
            DFSAdjacencyList::graph_rep(
              adjacency, g, row_ptrs, node_addrs, rows) *
            DFSAdjacencyList::visited(visited, g, visited_set_out)
     */
}
