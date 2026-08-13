#include "sll_project_def.h"



struct sll *nil_list()
/*@ Require emp
    Ensure sll(__return, nil)
*/
{
  return (struct sll *)0;
}

struct sll *new_list_node()
    /*@ Require emp
    Ensure __return != 0 &&
           store(&(__return -> data), 0) *
           store(&(__return -> next), 0)
*/;

struct sll *cons_list(unsigned int data, struct sll *next)
/*@ With l pt
    Require sll_pt(next, pt, l)
    Ensure exists pt_new,
           sll_pt(__return, pt_new, cons(data, l)) &&
           (l == nil && pt_new == &(__return -> next) || l != nil && pt_new == pt)
*/
{
  struct sll *node = new_list_node();
  node->data = data;
  node->next = next;
  return node;
}

void free_list_node(struct sll *p)
    /*@ Require exists d n, store(&(p -> data), d) * store(&(p -> next), n)
        Ensure emp
    */
    ;

void free_list(struct sll *head)
/*@ With l
    Require sll(head, l)
    Ensure emp
*/
{
  /*@ Inv exists l_rest, sll(head, l_rest) */
  while (head) {
    /*@ exists l_rest, head != 0 && sll(head, l_rest)
        which implies
        exists l_rest_new, l_rest == cons(head->data, l_rest_new) &&
       sll(head->next, l_rest_new)
    */
    struct sll *tmp = head;
    head = head->next;
    free_list_node(tmp);
  }
}

void map_list(struct sll *head, unsigned int x)
/*@ With l
    Require sll(head, l)
    Ensure sll(head, map_mult(x, l))
*/
{
  struct sll *p;
  /*@ Inv exists l1 l2, l == app(l1, l2) &&
          sllseg(head@pre, p, map_mult(x@pre, l1)) * sll(p, l2) &&
          head == head@pre && x == x@pre
  */
  for (p = head; p != (struct sll *)0; p = p->next) {
    /*@ Given l1 l2 */
    /*@ l == app(l1, l2) &&
            sllseg(head, p, map_mult(x, l1)) * sll(p, l2) &&
            p != 0
        which implies
        exists l2_new, l2 == cons(p->data, l2_new) &&
            sllseg(head, p, map_mult(x, l1)) * sll(p->next, l2_new)
    */
    p->data = x * p->data;
  }
}

struct sllb *new_sllb()
    /*@ Require emp
        Ensure __return != 0 &&
               store(&(__return -> head), 0) *
               store(&(__return -> ptail), 0)
    */
    ;

struct sllb *nil_list_box()
/*@ Require emp
    Ensure __return != 0 &&
           store(&(__return -> head), struct sll *, 0) *
           store(&(__return -> ptail), struct sll **, &(__return -> head))
*/
{
  struct sllb *box = new_sllb();
  box->head = nil_list();
  box->ptail = &box->head;
  return box;
}

struct sllb *cons_list_box(unsigned int data, struct sllb *box)
/*@ With l pt
    Require box != 0 &&
            (pt == &(box -> head) && l == nil || pt != &(box -> head) && l != nil) &&
            store(&(box -> ptail), struct sll **, pt) *
            sllbseg(&(box -> head), pt, l) *
            store(pt, struct sll *, 0)
    Ensure exists pt_new,
           __return != 0 &&
           store(&(__return -> ptail), struct sll **, pt_new) *
           sllbseg(&(__return -> head), pt_new, cons(data, l)) *
           store(pt_new, struct sll *, 0)
*/
{
  /*@ sllbseg(&(box -> head), pt, l) * store(pt, struct sll *, 0)
      which implies
      exists h, store(&(box -> head), struct sll *, h) * sll_pt(h, pt, l)
  */
  box->head = cons_list(data, box->head);
  if (box->ptail == &box->head) {
    box->ptail = &(box->head->next);
  }
  return box;
}

struct sllb *map_list_box(struct sllb *box, unsigned int x)
/*@ With l
    Require sllb_sll(box, l)
    Ensure sllb_sll(__return, map_mult(x, l))
*/
{
  /*@ sllb_sll(box, l)
      which implies
      exists h, box != 0 &&
          store(&(box -> head), struct sll *, h) *
          store(&(box -> ptail), struct sll **, 0) *
          sll(h, l)
  */
  map_list(box->head, x);
  return box;
}

void free_sllb(struct sllb *p)
    /*@ Require exists x y, p -> head == x && p -> ptail == y && emp
        Ensure emp
    */
    ;

void free_list_box(struct sllb *box)
/*@ With l
    Require sllb(box, l)
    Ensure emp
*/
{
  /*@ sllb(box, l)
      which implies
      exists h pt, box -> head == h && box -> ptail == pt && sll(h, l)
  */
  free_list(box->head);
  free_sllb(box);
}

struct sllb *app_list_box(struct sllb *b1, struct sllb *b2)
/*@ With l1 l2
    Require sllb(b1, l1) * sllb(b2, l2)
    Ensure sllb(__return, app(l1, l2))
*/
{
  /*@ sllb(b1, l1) * sllb(b2, l2)
      which implies
      exists pt1 h2 pt2,
          b1 != 0 && b2 != 0 &&
          store(&(b1 -> ptail), struct sll **, pt1) *
          sllbseg(&(b1 -> head), pt1, l1) * store(pt1, struct sll *, 0) *
          store(&(b2 -> head), struct sll *, h2) *
          store(&(b2 -> ptail), struct sll **, pt2) *
          sll_pt(h2, pt2, l2)
  */
  struct sll *h2 = b2->head;
  struct sll **pt2 = b2->ptail;
  *(b1->ptail) = h2;
  if (h2 != (struct sll *)0) {
    b1->ptail = pt2;
  }
  free_sllb(b2);
  return b1;
}

unsigned int sll_length(struct sll *head)
/*@ With l
    Require sll(head, l) && Zlength(l) <= 2147483647
    Ensure __return == Zlength(l) && sll(head@pre, l)
*/
{
  unsigned int len = 0;
  /*@ Inv exists l1 l2,
          l == app(l1, l2) &&
          len == Zlength(l1) &&
          sllseg(head@pre, head, l1) * sll(head, l2)
  */
  while (head) {
    /*@ exists l2, head != 0 && sll(head, l2)
        which implies
        exists l3, l2 == cons(head -> data, l3) && sll(head -> next, l3)
    */
    ++len;
    head = head->next;
  }
  return len;
}

unsigned int *new_uint_array(unsigned int n)
    /*@ With n0
        Require n == n0 && emp
        Ensure UIntArray::undef_seg(__return, 0, n0)
    */
    ;

unsigned int sll2array(struct sll *head, unsigned int **out_array)
/*@ With l
    Require sll(head, l) && Zlength(l) <= 2147483647 && undef_data_at(out_array,
   unsigned int *) Ensure exists arr_ret, sll(head@pre, l) &&
   store(out_array@pre, unsigned int *, arr_ret) &&
   UIntArray::full_shape(arr_ret, Zlength(l))
*/
{
  unsigned int len = sll_length(head);
  unsigned int *arr = new_uint_array(len);
  unsigned int i = 0;
  struct sll *p = head;
  /*@ Inv exists l1 l2,
          l == app(l1, l2) &&
          i == Zlength(l1) &&
          len == Zlength(l) &&
          0 <= i && i <= len &&
          sllseg(head@pre, p, l1) * sll(p, l2) *
          UIntArray::seg_shape(arr, 0, i) * UIntArray::undef_seg(arr, i, len)
  */
  while (p) {
    /*@ exists l1 l2, l == app(l1, l2) && p != 0 && i < len && sll(p, l2) *
            sllseg(head@pre, p, l1) * UIntArray::seg_shape(arr, 0, i) *
       UIntArray::undef_seg(arr, i, len) which implies exists l3, l2 == cons(p
       -> data, l3) && i < len && sll(p -> next, l3) * sllseg(head@pre, p, l1) *
       UIntArray::seg_shape(arr, 0, i) * UIntArray::undef_seg(arr, i, len)
    */
    arr[i] = p->data;
    i = i + 1;
    p = p->next;
  }
  *out_array = arr;
  return len;
}

unsigned int sllb2array(struct sllb *box, unsigned int **out_array)
/*@ With l
    Require sllb_sll(box, l) && Zlength(l) <= 2147483647 &&
            undef_data_at(out_array, unsigned int *)
    Ensure exists arr_ret,
           sllb_sll(box@pre, l) *
           store(out_array@pre, unsigned int *, arr_ret) *
           UIntArray::full_shape(arr_ret, Zlength(l))
*/
{
  /*@ sllb_sll(box, l)
      which implies
      exists h, box != 0 &&
          store(&(box -> head), struct sll *, h) *
          store(&(box -> ptail), struct sll **, 0) *
          sll(h, l)
  */
  return sll2array(box->head, out_array);
}
