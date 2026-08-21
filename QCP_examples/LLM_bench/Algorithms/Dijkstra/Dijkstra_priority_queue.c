#include "int_array_def.h"

#define MAX_VERTEX_COUNT 10
#define INF 1000000000
#define MAX_PRIORITY_QUEUE_SIZE 200005

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.Dijkstra.Dijkstra_priority_queue_lib */
/*@ Import Coq Import DijkstraGraph */
/*@ Import Coq Import DijkstraLinkedForwardStar */

/*@ Extern Coq
      (priority_queue_model :
        list Z -> list Z -> Z -> list (Z * Z) -> Prop)
      (priority_queue_push_result :
        list (Z * Z) -> list (Z * Z) -> Z -> Z -> Prop)
      (priority_queue_pop_result :
        list (Z * Z) -> list (Z * Z) -> Z -> Z -> Prop)
      (priority_queue_push_loop :
        list Z -> list Z -> Z -> Z -> list (Z * Z) -> Prop)
      (priority_queue_pop_loop :
        list Z -> list Z -> Z -> Z -> list (Z * Z) -> Prop)
 */

int priority_queue_vertex[MAX_PRIORITY_QUEUE_SIZE];
int priority_queue_distance[MAX_PRIORITY_QUEUE_SIZE];
int priority_queue_size;

void priority_queue_clear()
/*@ With (vertices : list Z) (distances : list Z)
         (size : Z) (items : list (Z * Z))
    Require
      priority_queue_model(vertices, distances, size, items) &&
      IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE, vertices) *
      IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE, distances) *
      store(&(priority_queue_size), int, size)
    Ensure
      exists vertices1 distances1,
        priority_queue_model(vertices1, distances1, 0, nil) &&
        IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE, vertices1) *
        IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE, distances1) *
        store(&(priority_queue_size), int, 0)
 */
{
  priority_queue_size = 0;
}

int priority_queue_empty()
/*@ With (vertices : list Z) (distances : list Z)
         (size : Z) (items : list (Z * Z))
    Require
      priority_queue_model(vertices, distances, size, items) &&
      IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE, vertices) *
      IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE, distances) *
      store(&(priority_queue_size), int, size)
    Ensure
      priority_queue_model(vertices, distances, size, items) &&
      ((__return == 1 && size == 0) || (__return == 0 && size != 0)) &&
      IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE, vertices) *
      IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE, distances) *
      store(&(priority_queue_size), int, size)
 */
{
  return priority_queue_size == 0;
}

void priority_queue_push(int vertex, int distance)
/*@ With (vertices : list Z) (distances : list Z)
         (size : Z) (items items_out : list (Z * Z))
    Require
      0 <= size && size < MAX_PRIORITY_QUEUE_SIZE &&
      0 <= vertex && vertex < MAX_VERTEX_COUNT &&
      0 <= distance && distance <= INF &&
      priority_queue_model(vertices, distances, size, items) &&
      priority_queue_push_result(items, items_out, vertex, distance) &&
      IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE, vertices) *
      IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE, distances) *
      store(&(priority_queue_size), int, size)
    Ensure
      exists vertices1 distances1,
        priority_queue_model(vertices1, distances1, size + 1, items_out) &&
        IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE, vertices1) *
        IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE, distances1) *
        store(&(priority_queue_size), int, size + 1)
 */
{
  int index = priority_queue_size;

  /*@ Inv Assert
      exists vertices_cur distances_cur items_cur,
        0 <= index && index <= priority_queue_size &&
        0 <= priority_queue_size &&
        priority_queue_size < MAX_PRIORITY_QUEUE_SIZE &&
        0 <= vertex && vertex < MAX_VERTEX_COUNT &&
        0 <= distance && distance <= INF &&
        priority_queue_push_loop(
          vertices_cur, distances_cur, priority_queue_size,
          index, items_cur) &&
        ((index == 0 &&
          IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE,
            vertices_cur) *
          IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE,
            distances_cur)) ||
         (0 < index &&
          IntArray::seg(
            priority_queue_vertex, 0, index - 1,
            sublist(0, index - 1, vertices_cur)) *
          store(pointer_offset(
            priority_queue_vertex, index - 1, sizeof(int), int), int,
            Znth(index - 1, vertices_cur, 0)) *
          store(pointer_offset(
            priority_queue_vertex, index, sizeof(int), int), int,
            Znth(index, vertices_cur, 0)) *
          IntArray::seg(
            priority_queue_vertex, index + 1, MAX_PRIORITY_QUEUE_SIZE,
            sublist(index + 1, MAX_PRIORITY_QUEUE_SIZE, vertices_cur)) *
          IntArray::seg(
            priority_queue_distance, 0, index - 1,
            sublist(0, index - 1, distances_cur)) *
          store(pointer_offset(
            priority_queue_distance, index - 1, sizeof(int), int), int,
            Znth(index - 1, distances_cur, 0)) *
          store(pointer_offset(
            priority_queue_distance, index, sizeof(int), int), int,
            Znth(index, distances_cur, 0)) *
          IntArray::seg(
            priority_queue_distance, index + 1, MAX_PRIORITY_QUEUE_SIZE,
            sublist(index + 1, MAX_PRIORITY_QUEUE_SIZE, distances_cur))))
   */
  while (index > 0 && priority_queue_distance[index - 1] > distance) {
    priority_queue_vertex[index] = priority_queue_vertex[index - 1];
    priority_queue_distance[index] = priority_queue_distance[index - 1];
    index = index - 1;
  }

  priority_queue_vertex[index] = vertex;
  priority_queue_distance[index] = distance;
  priority_queue_size = priority_queue_size + 1;
}

void priority_queue_pop(int *vertex_out, int *distance_out)
/*@ With (vertices : list Z) (distances : list Z)
         (size : Z) (items items_out : list (Z * Z))
         (vertex distance : Z)
    Require
      0 < size && size <= MAX_PRIORITY_QUEUE_SIZE &&
      priority_queue_model(vertices, distances, size, items) &&
      priority_queue_pop_result(items, items_out, vertex, distance) &&
      IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE, vertices) *
      IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE, distances) *
      store(&(priority_queue_size), int, size) *
      has_int_permission(vertex_out) *
      has_int_permission(distance_out)
    Ensure
      exists vertices1 distances1,
        *vertex_out == vertex &&
        *distance_out == distance &&
        priority_queue_model(vertices1, distances1, size - 1, items_out) &&
        IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE, vertices1) *
        IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE, distances1) *
        store(&(priority_queue_size), int, size - 1)
 */
{
  int index = 1;

  *vertex_out = priority_queue_vertex[0];
  *distance_out = priority_queue_distance[0];

  /*@ Inv Assert
      exists vertices_cur distances_cur items_cur,
        1 <= index && index <= priority_queue_size &&
        0 < priority_queue_size &&
        priority_queue_size <= MAX_PRIORITY_QUEUE_SIZE &&
        priority_queue_pop_loop(
          vertices_cur, distances_cur, priority_queue_size,
          index, items_cur) &&
        ((index == priority_queue_size &&
          IntArray::full(priority_queue_vertex, MAX_PRIORITY_QUEUE_SIZE,
            vertices_cur) *
          IntArray::full(priority_queue_distance, MAX_PRIORITY_QUEUE_SIZE,
            distances_cur)) ||
         (index < priority_queue_size &&
          IntArray::seg(
            priority_queue_vertex, 0, index - 1,
            sublist(0, index - 1, vertices_cur)) *
          store(pointer_offset(
            priority_queue_vertex, index - 1, sizeof(int), int), int,
            Znth(index - 1, vertices_cur, 0)) *
          store(pointer_offset(
            priority_queue_vertex, index, sizeof(int), int), int,
            Znth(index, vertices_cur, 0)) *
          IntArray::seg(
            priority_queue_vertex, index + 1, MAX_PRIORITY_QUEUE_SIZE,
            sublist(index + 1, MAX_PRIORITY_QUEUE_SIZE, vertices_cur)) *
          IntArray::seg(
            priority_queue_distance, 0, index - 1,
            sublist(0, index - 1, distances_cur)) *
          store(pointer_offset(
            priority_queue_distance, index - 1, sizeof(int), int), int,
            Znth(index - 1, distances_cur, 0)) *
          store(pointer_offset(
            priority_queue_distance, index, sizeof(int), int), int,
            Znth(index, distances_cur, 0)) *
          IntArray::seg(
            priority_queue_distance, index + 1, MAX_PRIORITY_QUEUE_SIZE,
            sublist(index + 1, MAX_PRIORITY_QUEUE_SIZE, distances_cur)))) *
        store(vertex_out, int, *vertex_out) *
        store(distance_out, int, *distance_out)
   */
  while (index < priority_queue_size) {
    priority_queue_vertex[index - 1] = priority_queue_vertex[index];
    priority_queue_distance[index - 1] = priority_queue_distance[index];
    index = index + 1;
  }

  priority_queue_size = priority_queue_size - 1;
}
