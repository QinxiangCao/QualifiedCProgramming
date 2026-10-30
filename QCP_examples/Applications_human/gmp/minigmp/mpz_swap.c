#include "gmp/minigmp/gmp_def.h"
void int_swap(int *x, int *y)
/*@
  With
    px py
  Require
    *x == px && *y == py
  Ensure
    *x == py && *y == px
*/;

void mp_ptr_swap(unsigned int **x, unsigned int **y)
/*@
  With
    px py
  Require
    *x == px && *y == py
  Ensure
    *x == py && *y == px
*/;

void
mpz_swap (mpz_ptr u, mpz_ptr v)
/*@ plain
  With
    n m
  Require
    store_Z(u, n) * store_Z(v, m)
  Ensure
    store_Z(u, m) * store_Z(v, n)
*/;

void
mpz_swap (mpz_ptr u, mpz_ptr v)
/*@ u_read0
  With
    n m
  Require
    store_Z_read0(u, n) * store_Z(v, m)
  Ensure
    store_Z(u, m) * store_Z_read0(v, n)
*/
;

void
mpz_swap (mpz_ptr u, mpz_ptr v)
/*@ plain */
/*@ u_read0 */
{
  /*@ Assert exists uptr usize ucap vptr vsize vcap,
      u == u@pre &&
      v == v@pre &&
      Zabs(usize) <= ucap &&
      same_sign(n_u_read0, usize) &&
      Zabs(vsize) <= vcap &&
      same_sign(m_u_read0, vsize) &&
      mpd_store_Z_compact_read0(uptr, Zabs(n_u_read0), Zabs(usize)) *
      UIntArray::undef_seg(uptr, Zmax(Zabs(usize), 1), ucap) *
      store(&(u->_mp_size), usize) *
      store(&(u->_mp_alloc), ucap) *
      store(&(u->_mp_d), unsigned int *, uptr) *
      mpd_store_Z_compact(UINT_MOD, vptr, Zabs(m_u_read0), Zabs(vsize)) *
      UIntArray::undef_seg(vptr, Zabs(vsize), vcap) *
      store(&(v->_mp_size), vsize) *
      store(&(v->_mp_alloc), vcap) *
      store(&(v->_mp_d), unsigned int *, vptr)
  $ u_read0 */
  int_swap (&u->_mp_alloc, &v->_mp_alloc);
  mp_ptr_swap(&u->_mp_d, &v->_mp_d);
  int_swap (&u->_mp_size, &v->_mp_size);
  /*@ Assert
      u == u@pre && v == v@pre &&
      store_Z(u, m_u_read0) * store_Z_read0(v, n_u_read0)
  $ u_read0 */
}
