/**************************************************************************************************
MiniSat -- Copyright (c) 2005, Niklas Sorensson
http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat/

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/
// Modified to compile with MS Visual Studio 6.0 by Alan Mishchenko


/* Conflict analysis and learned-clause minimization. */
#include "solver_qcp_internal.h"

/* A successful reason-graph traversal certifies that the learned literal is
   redundant. Failed traversals undo newly added tags. */
static bool solver_lit_removable(solver* s, lit l, unsigned int minl)
/*@ With reasons_ptr levels_ptr trail_ptr tags_ptr lrm_wl
          (lrm_n : Z) (lrm_F : cnf) (lrm_A_arr : list literal)
          (lrm_K : solver_propagation_context) (M : msolver) lrm_focus
    Require (0 <= minl && minl <= UINT_MAX && solver_shape(M) &&
            analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
            msolver_seed_shadow(M) &&
            0 <= lit_var_c(l) && lit_var_c(l) < lrm_n &&
            In(lit_var_c(l), map(lit_var_c, mt_trail(ms_core(M)))) &&
            In(lit_var_c(l), ms_tagged(M)) &&
            assigned_below_current(
              msolver_view(lrm_n, M), lit_var_c(l)) &&
            Znth(lit_var_c(l), ms_reason_words(M), 0) != 0 &&
            analysis_tags_exact(lrm_n, ms_tags(M), ms_tagged(M)) &&
            2 * lrm_n <= INT_MAX &&
            store(&(s->reasons), reasons_ptr) *
            PtrArray::seg(reasons_ptr, 0, lrm_n, ms_reason_words(M)) *
            solver_ptr_tail(reasons_ptr, lrm_n, ms_cap(M)) *
            store(&(s->levels), levels_ptr) *
            IntArray::seg(levels_ptr, 0, lrm_n, mt_levels(ms_core(M))) *
            solver_int_tail(levels_ptr, lrm_n, ms_cap(M)) *
            solver_reason_levels_frame_at(s, M, trail_ptr, tags_ptr, lrm_wl)) *
            store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&true, int, 1) * store(&false, int, 0)
    Ensure (solver_lit_removable_post(
             s, l, reasons_ptr, levels_ptr, trail_ptr, tags_ptr,
             lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus, __return, lrm_wl)) *
            store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&true, int, 1) * store(&false, int, 0)
 */
{
    /*@ solver_shape(M) &&
          analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
          msolver_seed_shadow(M) &&
          0 <= lit_var_c(l) && lit_var_c(l) < lrm_n &&
          0 <= minl && minl <= UINT_MAX &&
          assigned_below_current(
            msolver_view(lrm_n, M), lit_var_c(l)) &&
          Znth(lit_var_c(l), ms_reason_words(M), 0) != 0 &&
          analysis_tags_exact(lrm_n, ms_tags(M), ms_tagged(M)) &&
          2 * lrm_n <= INT_MAX &&
          store(&(s->reasons), reasons_ptr) *
          PtrArray::seg(reasons_ptr, 0, lrm_n, ms_reason_words(M)) *
          solver_ptr_tail(reasons_ptr, lrm_n, ms_cap(M)) *
          store(&(s->levels), levels_ptr) *
          IntArray::seg(levels_ptr, 0, lrm_n, mt_levels(ms_core(M))) *
          solver_int_tail(levels_ptr, lrm_n, ms_cap(M)) *
          solver_reason_levels_frame_at(s, M, trail_ptr, tags_ptr, lrm_wl)
        which implies exists (Croot : clause),
          analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
          msolver_seed_shadow(M) &&
          0 <= lit_var_c(l) && lit_var_c(l) < lrm_n &&
          0 <= minl && minl <= UINT_MAX && 2 * lrm_n <= INT_MAX &&
          assigned_below_current(
            msolver_view(lrm_n, M), lit_var_c(l)) &&
          Znth(lit_var_c(l), ms_reason_words(M), 0) != 0 &&
          reason_target_wf(
            lrm_n, M, lit_var_c(l),
            Znth(lit_var_c(l), ms_reason_words(M), 0), Croot) &&
          analysis_tags_exact(lrm_n, ms_tags(M), ms_tagged(M)) &&
          store(&(s->size), lrm_n) *
          store(&(s->reasons), reasons_ptr) *
          store(&(s->levels), levels_ptr) *
          store(&(s->tags), tags_ptr) *
          PtrArray::seg(reasons_ptr, 0, lrm_n, ms_reason_words(M)) *
          solver_ptr_tail(reasons_ptr, lrm_n, ms_cap(M)) *
          IntArray::seg(levels_ptr, 0, lrm_n, mt_levels(ms_core(M))) *
          solver_int_tail(levels_ptr, lrm_n, ms_cap(M)) *
          CharArray::seg(tags_ptr, 0, lrm_n, ms_tags(M)) *
          solver_char_tail(tags_ptr, lrm_n, ms_cap(M)) *
          Veci::rep(&(s->tagged), ms_tagged(M)) *
          Veci::rep(&(s->stack), ms_stack(M)) *
          clause_db_rep(ms_prob(M)) * clause_db_rep(ms_learnt(M)) *
          binary_scratch_rep(ms_binary(M), ms_binary_lits(M)) *
          solver_removable_frame_at(s, M, trail_ptr, lrm_wl)
     */
    lbool*   tags    = s->tags;
    clause** reasons = s->reasons;
    int*     levels  = s->levels;
    int      top     = veci_size(&s->tagged);

    assert(lit_var(l) /*@ where(original) */ >= 0 && lit_var(l) /*@ where(original) */ < s->size);
    /*@ 0 <= lit_var_c(l) && lit_var_c(l) < lrm_n &&
          PtrArray::seg(reasons_ptr, 0, lrm_n, ms_reason_words(M))
        which implies
          store(pointer_offset(
                  reasons_ptr, lit_var_c(l), clause *),
                clause *,
                Znth(lit_var_c(l), ms_reason_words(M), 0)) *
          removable_reason_array_hole(
            reasons_ptr, lit_var_c(l), lrm_n, ms_reason_words(M))
     */
    assert(reasons[lit_var(l) /*@ where(original) */] != 0);
    veci_resize(&s->stack,0);
    veci_push(&s->stack,lit_var(l) /*@ where(original) */);

    /*@ Inv Assert (exists tags_now tagged_now stack_now done,
          s == s@pre && l == l@pre && minl == minl@pre &&
          tags == tags_ptr && reasons == reasons_ptr &&
          levels == levels_ptr &&
          top == Zlength(ms_tagged(M)) &&
          analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
          msolver_seed_shadow(M) &&
          2 * lrm_n <= INT_MAX &&
          analysis_tags_exact(lrm_n, ms_tags(M), ms_tagged(M)) &&
          analysis_tags_exact(lrm_n, tags_now, tagged_now) &&
          incl(stack_now, map(lit_var_c, mt_trail(ms_core(M)))) &&
          In(lit_var_c(l@pre), ms_tagged(M)) &&
          removable_dfs_loop_inv(lrm_n, M, l@pre, minl@pre, ms_tagged(M),
                                  tags_now, tagged_now, stack_now, done) &&
          store(&(s->size), lrm_n) *
          store(&(s->reasons), reasons_ptr) *
          store(&(s->levels), levels_ptr) *
          store(&(s->tags), tags_ptr) *
          PtrArray::seg(reasons_ptr, 0, lrm_n, ms_reason_words(M)) *
          solver_ptr_tail(reasons_ptr, lrm_n, ms_cap(M)) *
          IntArray::seg(levels_ptr, 0, lrm_n, mt_levels(ms_core(M))) *
          solver_int_tail(levels_ptr, lrm_n, ms_cap(M)) *
          CharArray::seg(tags_ptr, 0, lrm_n, tags_now) *
          solver_char_tail(tags_ptr, lrm_n, ms_cap(M)) *
          Veci::rep(&(s->tagged), tagged_now) *
          Veci::rep(&(s->stack), stack_now) *
          clause_db_rep(ms_prob(M)) * clause_db_rep(ms_learnt(M)) *
          binary_scratch_rep(ms_binary(M), ms_binary_lits(M)) *
          solver_removable_frame_at(s, M, trail_ptr, lrm_wl)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&true, int, 1) * store(&false, int, 0)
     */
    while (veci_size(&s->stack) > 0){
        /*@ Given tags_now tagged_now stack_now done */
        clause* c;
        int v = veci_begin(&s->stack)[veci_size(&s->stack)-1];
        /*@ 0 < Zlength(stack_now) &&
              v == Znth(Zlength(stack_now) - 1, stack_now, 0)
            by local */
        /*@ removable_dfs_loop_inv(
              lrm_n, M, l@pre, minl@pre, ms_tagged(M), tags_now,
              tagged_now, stack_now, done) &&
            analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
            0 < Zlength(stack_now) &&
            v == Znth(Zlength(stack_now) - 1, stack_now, 0)
            which implies exists (Cnext : clause),
              removable_dfs_loop_inv(
                lrm_n, M, l@pre, minl@pre, ms_tagged(M), tags_now,
                tagged_now, stack_now, done) &&
              analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
              0 < Zlength(stack_now) &&
              v == Znth(Zlength(stack_now) - 1, stack_now, 0) &&
              0 <= v && v < lrm_n &&
              Znth(v, ms_reason_words(M), 0) != 0 &&
              removable_reason_focus(
                lrm_n, M, v, Znth(v, ms_reason_words(M), 0), Cnext)
         */
        /*@ Given Cnext */
        assert(v >= 0 && v < s->size);
        veci_resize(&s->stack,veci_size(&s->stack)-1);
        /*@ removable_dfs_loop_inv(
              lrm_n, M, l@pre, minl@pre, ms_tagged(M), tags_now,
              tagged_now, stack_now, done) &&
            0 < Zlength(stack_now) &&
            v == Znth(Zlength(stack_now) - 1, stack_now, 0)
            which implies exists (stack_after : list Z),
              removable_dfs_loop_inv(
                lrm_n, M, l@pre, minl@pre, ms_tagged(M), tags_now,
                tagged_now, stack_now, done) &&
              stack_after ==
                sublist(0, Zlength(stack_now) - 1, stack_now) &&
              stack_now == app(stack_after, cons(v, nil))
         */
        /*@ Given stack_after */
        /*@ 0 <= v && v < lrm_n &&
              PtrArray::seg(reasons_ptr, 0, lrm_n, ms_reason_words(M))
            which implies
              store(pointer_offset(
                      reasons_ptr, v, clause *),
                    clause *, Znth(v, ms_reason_words(M), 0)) *
              removable_reason_array_hole(
                reasons_ptr, v, lrm_n, ms_reason_words(M))
         */
        assert(reasons[v] != 0);
        c    = reasons[v];
        /*@ 0 <= v &&
              store(pointer_offset(
                      reasons_ptr, v,
                      struct clause_t *),
                    struct clause_t *, Znth(v, ms_reason_words(M), 0)) *
              removable_reason_array_hole(
                reasons_ptr, v, lrm_n, ms_reason_words(M))
            which implies
              0 <= v &&
              PtrArray::seg(reasons_ptr, 0, lrm_n, ms_reason_words(M))
         */

        /*@ c == Znth(v, ms_reason_words(M), 0) by local */

        if (clause_is_lit(c)){
            /*@ analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                  removable_reason_focus(lrm_n, M, v, c, Cnext) &&
                  is_tag(c) == msat_true
                which implies
                  removable_reason_focus(lrm_n, M, v, c, Cnext) &&
                  is_tag(c) == msat_true &&
                  0 <= lit_var_c(tag_lit(c)) &&
                  lit_var_c(tag_lit(c)) < lrm_n
             */
            int v = lit_var(clause_read_lit(c)) /*@ where(original) */;
            /*@ 0 <= v && v < lrm_n &&
                  CharArray::seg(tags_ptr, 0, lrm_n, tags_now)
                which implies
                  store(pointer_offset(
                          tags_ptr, v, char),
                        char, Znth(v, tags_now, 0)) *
                  CharArray::missing_i(tags_ptr, v, 0, lrm_n, tags_now)
             */
            /*@ 0 <= v && v < lrm_n &&
                  IntArray::seg(levels_ptr, 0, lrm_n, mt_levels(ms_core(M)))
                which implies
                  store(pointer_offset(
                          levels_ptr, v, int),
                        int, Znth(v, mt_levels(ms_core(M)), 0)) *
                  IntArray::missing_i(
                    levels_ptr, v, 0, lrm_n, mt_levels(ms_core(M)))
             */
            /*@ 0 <= v && v < lrm_n &&
                  PtrArray::seg(reasons_ptr, 0, lrm_n, ms_reason_words(M))
                which implies
                  store(pointer_offset(
                          reasons_ptr, v,
                          struct clause_t *),
                        struct clause_t *,
                        Znth(v, ms_reason_words(M), 0)) *
                  PtrArray::missing_i(
                    reasons_ptr, v, 0, lrm_n, ms_reason_words(M))
             */
            if (tags[v] == l_Undef && levels[v] != 0){
                if (reasons[v] != 0 && ((1U << (levels[v] & 31)) & minl)){
                    /*@ analysis_cancel_ready(
                          lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                        analysis_tags_exact(lrm_n, tags_now, tagged_now) &&
                        0 <= v && v < lrm_n &&
                        Znth(v, tags_now, 0) == 0 &&
                        Znth(v, ms_reason_words(M), 0) != 0
                        which implies exists (Cpush : clause),
                          analysis_cancel_ready(
                            lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                          analysis_tags_exact(lrm_n, tags_now, tagged_now) &&
                          0 <= v && v < lrm_n &&
                          Znth(v, tags_now, 0) == 0 &&
                          Znth(v, ms_reason_words(M), 0) != 0 &&
                          Zlength(tagged_now) < lrm_n &&
                          reason_target_wf(
                            lrm_n, M, v, Znth(v, ms_reason_words(M), 0), Cpush)
                     */
                    /*@ Given Cpush */
                    /*@ analysis_cancel_ready(
                          lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                        removable_dfs_loop_inv(
                          lrm_n, M, l@pre, minl@pre, ms_tagged(M), tags_now,
                          tagged_now, stack_now, done) &&
                        0 < Zlength(stack_now) &&
                        stack_after ==
                          sublist(0, Zlength(stack_now) - 1, stack_now)
                        which implies
                          analysis_cancel_ready(
                            lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                          removable_dfs_loop_inv(
                            lrm_n, M, l@pre, minl@pre, ms_tagged(M), tags_now,
                            tagged_now, stack_now, done) &&
                          Zlength(stack_after) < lrm_n &&
                          Zlength(sublist(
                            0, Zlength(stack_now) - 1,
                            app(stack_after,
                                cons(Znth(Zlength(stack_now) - 1,
                                          stack_now, 0), nil)))) < lrm_n
                     */
                    veci_push(&s->stack,v);
                    tags[v] = l_True;
                    veci_push(&s->tagged,v);
                }else{
                    int* tagged = veci_begin(&s->tagged);
                    int j;
                    /*@ Inv Assert (exists tags_rollback,
                          s == s@pre && l == l@pre && minl == minl@pre &&
                          tags == tags_ptr &&
                          top == Zlength(ms_tagged(M)) &&
                          0 <= j && j <= Zlength(tagged_now) &&
                          (j == Zlength(tagged_now) ||
                           (j < Zlength(tagged_now) &&
                            0 <= tagged_now[j] &&
                            tagged_now[j] < lrm_n)) &&
                          analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                          msolver_seed_shadow(M) &&
                          removable_rollback_inv(
                            lrm_n, top, j, ms_tagged(M), ms_tags(M), tags_now,
                            tagged_now, tags_rollback) &&
                          store(&(s->tags), tags_ptr) *
                          CharArray::seg(tags_ptr, 0, lrm_n, tags_rollback) *
                          solver_char_tail(tags_ptr, lrm_n, ms_cap(M)) *
                          Veci::rep_ptr(&(s->tagged), tagged, tagged_now) *
                          store(&(s->size), lrm_n) *
                          store(&(s->reasons), reasons_ptr) *
                          store(&(s->levels), levels_ptr) *
                          PtrArray::seg(reasons_ptr, 0, lrm_n,
                                        ms_reason_words(M)) *
                          solver_ptr_tail(reasons_ptr, lrm_n, ms_cap(M)) *
                          IntArray::seg(levels_ptr, 0, lrm_n,
                                        mt_levels(ms_core(M))) *
                          solver_int_tail(levels_ptr, lrm_n, ms_cap(M)) *
                          Veci::rep(&(s->stack), stack_after) *
                          clause_db_rep(ms_prob(M)) *
                          clause_db_rep(ms_learnt(M)) *
                          binary_scratch_rep(ms_binary(M), ms_binary_lits(M)) *
                          has_permission(&#v) *
                          has_permission(&v) *
                          has_permission(&c) *
                          has_permission(&reasons) *
                          has_permission(&levels) *
                          solver_removable_frame_at(s, M, trail_ptr, lrm_wl)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&true, int, 1) * store(&false, int, 0)
                     */
                    for (j = top; j < veci_size(&s->tagged); j++)
                        /*@ Given tags_rollback */
                        /*@ 0 <= tagged_now[j - 0] &&
                              tagged_now[j - 0] < lrm_n &&
                              CharArray::seg(tags_ptr, 0, lrm_n, tags_rollback)
                            which implies exists old_tag,
                              store(pointer_offset(
                                      tags_ptr, tagged_now[j - 0], char), char, old_tag) *
                              CharArray::missing_i(
                                tags_ptr, tagged_now[j - 0], 0, lrm_n,
                                tags_rollback)
                         */
                        tags[tagged[j]] = l_Undef;
                    veci_resize(&s->tagged,top);
                    return false;
                }
            }
        }else{
            /*@ analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                  removable_reason_focus(lrm_n, M, v, c, Cnext) &&
                  is_tag(c) == msat_false &&
                  clause_db_rep(ms_prob(M)) * clause_db_rep(ms_learnt(M))
                which implies exists (is_learnt_now : bool)
                  (clause_words : list Z),
                  is_tag(c) == msat_false &&
                  analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                  removable_reason_focus(lrm_n, M, v, c, Cnext) &&
                  Cnext == lits_denote(clause_words) &&
                  Forall(lit_wf_c(lrm_n), clause_words) &&
                  clause_hdr_word(is_learnt_now,
                    Zlength(clause_words)) / 2 == Zlength(clause_words) &&
                  store(clause_hdr_addr(c), int,
                        clause_hdr_word(is_learnt_now,
                                        Zlength(clause_words))) *
                  activity_state(c, is_learnt_now, Zlength(clause_words)) *
                  IntArray::seg(clause_lits_addr(c), 0,
                                Zlength(clause_words), clause_words) *
                  clause_db_pair_remainder(ms_prob(M), ms_learnt(M), c,
                                           is_learnt_now, clause_words)
             */
            /*@ Given is_learnt_now clause_words */
            lit*    lits = clause_begin(c);
            int     i, j;

            /*@ Inv Assert (exists tags_scan tagged_scan stack_scan done_scan,
                  s == s@pre && l == l@pre && minl == minl@pre &&
                  tags == tags_ptr && reasons == reasons_ptr &&
                  levels == levels_ptr &&
                  top == Zlength(ms_tagged(M)) &&
                  lits == clause_lits_addr(c) &&
                  clause_lits_pointer(c, lits) &&
                  c % 2 == 0 &&
                  analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                  msolver_seed_shadow(M) &&
                  2 * lrm_n <= INT_MAX &&
                  analysis_tags_exact(lrm_n, ms_tags(M), ms_tagged(M)) &&
                  analysis_tags_exact(lrm_n, tags_scan, tagged_scan) &&
                  incl(cons(v, stack_scan),
                       map(lit_var_c, mt_trail(ms_core(M)))) &&
                  In(lit_var_c(l@pre), ms_tagged(M)) &&
                  removable_reason_scan_inv(
                    lrm_n, M, l@pre, minl@pre, ms_tagged(M), done_scan, stack_scan,
                    tags_scan, tagged_scan, Cnext, v, c, i) &&
                  1 <= i && i <= Zlength(clause_words) &&
                  Forall(lit_wf_c(lrm_n), clause_words) &&
                  clause_hdr_word(is_learnt_now, Zlength(clause_words)) / 2 ==
                    Zlength(clause_words) &&
                  Cnext == lits_denote(clause_words) &&
                  store(&(s->size), lrm_n) *
                  store(&(s->reasons), reasons_ptr) *
                  store(&(s->levels), levels_ptr) *
                  store(&(s->tags), tags_ptr) *
                  PtrArray::seg(reasons_ptr, 0, lrm_n, ms_reason_words(M)) *
                  solver_ptr_tail(reasons_ptr, lrm_n, ms_cap(M)) *
                  IntArray::seg(levels_ptr, 0, lrm_n, mt_levels(ms_core(M))) *
                  solver_int_tail(levels_ptr, lrm_n, ms_cap(M)) *
                  CharArray::seg(tags_ptr, 0, lrm_n, tags_scan) *
                  solver_char_tail(tags_ptr, lrm_n, ms_cap(M)) *
                  Veci::rep(&(s->tagged), tagged_scan) *
                  Veci::rep(&(s->stack), stack_scan) *
                  store(clause_hdr_addr(c), int,
                        clause_hdr_word(is_learnt_now,
                                        Zlength(clause_words))) *
                  activity_state(c, is_learnt_now, Zlength(clause_words)) *
                  IntArray::seg(clause_lits_addr(c), 0,
                                Zlength(clause_words),
                                clause_words) *
                  clause_db_pair_remainder(ms_prob(M), ms_learnt(M),
                                           c, is_learnt_now, clause_words) *
                  binary_scratch_rep(ms_binary(M), ms_binary_lits(M)) *
                  solver_removable_frame_at(s, M, trail_ptr, lrm_wl) *
                  has_permission(&j)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&true, int, 1) * store(&false, int, 0)
             */
            for (i = 1; i < clause_size(c); i++){
                /*@ Given tags_scan tagged_scan stack_scan done_scan */
                /*@ analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                      removable_reason_scan_inv(
                        lrm_n, M, l@pre, minl@pre, ms_tagged(M), done_scan,
                        stack_scan, tags_scan, tagged_scan, Cnext, v, c, i)
                    which implies
                      analysis_cancel_ready(lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                      removable_reason_scan_inv(
                        lrm_n, M, l@pre, minl@pre, ms_tagged(M), done_scan,
                        stack_scan, tags_scan, tagged_scan, Cnext, v, c, i) &&
                      Zlength(stack_scan) < lrm_n
                 */
                /*@ Forall(lit_wf_c(lrm_n), clause_words) &&
                      0 <= i && i < Zlength(clause_words)
                    which implies
                      Forall(lit_wf_c(lrm_n), clause_words) &&
                      0 <= i && i < Zlength(clause_words) &&
                      0 <= lit_var_c(Znth(i, clause_words, 0)) &&
                      lit_var_c(Znth(i, clause_words, 0)) < lrm_n
                 */
                int v = lit_var(lits[i]) /*@ where(original) */;
                /*@ 0 <= v && v < lrm_n by local */
                if (tags[v] == l_Undef && levels[v] != 0){
                    if (reasons[v] != 0 && ((1U << (levels[v] & 31)) & minl)){
                        /*@ analysis_cancel_ready(
                              lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                            msolver_seed_shadow(M) &&
                            analysis_tags_exact(lrm_n, tags_scan, tagged_scan) &&
                            0 <= v && v < lrm_n &&
                            Znth(v, tags_scan, 0) == 0 &&
                            Znth(v, ms_reason_words(M), 0) != 0 &&
                            Zlength(stack_scan) < lrm_n
                            which implies exists (Cpush : clause),
                              analysis_cancel_ready(
                                lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                              msolver_seed_shadow(M) &&
                              analysis_tags_exact(lrm_n, tags_scan, tagged_scan) &&
                              0 <= v && v < lrm_n &&
                              Znth(v, tags_scan, 0) == 0 &&
                              Znth(v, ms_reason_words(M), 0) != 0 &&
                              Zlength(stack_scan) < lrm_n &&
                              Zlength(tagged_scan) < lrm_n &&
                              reason_target_wf(
                                lrm_n, M, v, Znth(v, ms_reason_words(M), 0),
                                Cpush)
                         */
                        veci_push(&s->stack,lit_var(lits[i]) /*@ where(original) */);
                        tags[v] = l_True;
                        veci_push(&s->tagged,v);
                    }else{
                        int* tagged = veci_begin(&s->tagged);
                        /*@ Inv Assert (exists tags_rollback,
                              s == s@pre && l == l@pre &&
                              minl == minl@pre && tags == tags_ptr &&
                              top == Zlength(ms_tagged(M)) &&
                              0 <= j && j <= Zlength(tagged_scan) &&
                              (j == Zlength(tagged_scan) ||
                               (j < Zlength(tagged_scan) &&
                                0 <= tagged_scan[j] &&
                                tagged_scan[j] < lrm_n)) &&
                              analysis_cancel_ready(
                                lrm_n, lrm_F, lrm_A_arr, lrm_K, M, lrm_focus) &&
                              msolver_seed_shadow(M) &&
                              removable_rollback_inv(
                                lrm_n, top, j, ms_tagged(M), ms_tags(M),
                                tags_scan, tagged_scan, tags_rollback) &&
                              store(&(s->tags), tags_ptr) *
                              CharArray::seg(tags_ptr, 0, lrm_n,
                                             tags_rollback) *
                              solver_char_tail(tags_ptr, lrm_n, ms_cap(M)) *
                              Veci::rep_ptr(&(s->tagged), tagged, tagged_scan) *
                              store(&(s->size), lrm_n) *
                              store(&(s->reasons), reasons_ptr) *
                              store(&(s->levels), levels_ptr) *
                              PtrArray::seg(reasons_ptr, 0, lrm_n,
                                            ms_reason_words(M)) *
                              solver_ptr_tail(reasons_ptr, lrm_n, ms_cap(M)) *
                              IntArray::seg(levels_ptr, 0, lrm_n,
                                            mt_levels(ms_core(M))) *
                              solver_int_tail(levels_ptr, lrm_n, ms_cap(M)) *
                              Veci::rep(&(s->stack), stack_scan) *
                              store(clause_hdr_addr(c), int,
                                    clause_hdr_word(is_learnt_now,
                                      Zlength(clause_words))) *
                              store(&lits, lit *, clause_lits_addr(c)) *
                              activity_state(c, is_learnt_now, Zlength(clause_words)) *
                              IntArray::seg(clause_lits_addr(c), 0,
                                            Zlength(clause_words),
                                            clause_words) *
                              clause_db_pair_remainder(
                                ms_prob(M), ms_learnt(M), c,
                                is_learnt_now, clause_words) *
                              binary_scratch_rep(ms_binary(M), ms_binary_lits(M)) *
                              has_permission(&#v) *
                              has_permission(&v) *
                              has_permission(&i) *
                              has_permission(&reasons) *
                              has_permission(&levels) *
                              solver_removable_frame_at(s, M, trail_ptr, lrm_wl)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&true, int, 1) * store(&false, int, 0)
                         */
                        for (j = top; j < veci_size(&s->tagged); j++)
                            /*@ Given tags_rollback */
                            /*@ 0 <= tagged_scan[j - 0] &&
                                  tagged_scan[j - 0] < lrm_n &&
                                  CharArray::seg(
                                    tags_ptr, 0, lrm_n, tags_rollback)
                                which implies exists old_tag,
                                  store(pointer_offset(
                                          tags_ptr, tagged_scan[j - 0], char), char, old_tag) *
                                  CharArray::missing_i(
                                    tags_ptr, tagged_scan[j - 0], 0, lrm_n,
                                    tags_rollback)
                             */
                            tags[tagged[j]] = l_Undef;
                        veci_resize(&s->tagged,top);
                        /*@ exists c_refold lits_refold,
                              0 < c_refold && c_refold % 2 == 0 &&
                              lits_refold == clause_lits_addr(c_refold) &&
                              clause_lits_pointer(c_refold, lits_refold) &&
                              store(&c, clause *, c_refold) *
                              store(&lits, lit *, lits_refold) *
                              store(clause_hdr_addr(c_refold), int,
                                  clause_hdr_word(is_learnt_now,
                                                  Zlength(clause_words))) *
                              activity_state(c_refold, is_learnt_now, Zlength(clause_words)) *
                              IntArray::seg(lits_refold, 0,
                                            Zlength(clause_words),
                                            clause_words) *
                              clause_db_pair_remainder(
                                ms_prob(M), ms_learnt(M), c_refold,
                                is_learnt_now, clause_words)
                            which implies
                              MiniSatClause::rep(c_refold, is_learnt_now,
                                                 clause_words) *
                              clause_db_pair_remainder(
                                ms_prob(M), ms_learnt(M), c_refold,
                                is_learnt_now, clause_words) *
                              store(&c, clause *, c_refold) *
                              store(&lits, lit *, lits_refold)
                         */
                        return false;
                    }
                }
            }
            /*@ 0 < c && c % 2 == 0 &&
                  lits == clause_lits_addr(c) &&
                  clause_lits_pointer(c, lits) &&
                  store(clause_hdr_addr(c), int,
                      clause_hdr_word(is_learnt_now,
                                      Zlength(clause_words))) *
                  activity_state(c, is_learnt_now, Zlength(clause_words)) *
                  IntArray::seg(lits, 0,
                                Zlength(clause_words),
                                clause_words) *
                  clause_db_pair_remainder(ms_prob(M), ms_learnt(M), c,
                                           is_learnt_now, clause_words)
                which implies
                  MiniSatClause::rep(c, is_learnt_now, clause_words) *
                  clause_db_pair_remainder(ms_prob(M), ms_learnt(M), c,
                                           is_learnt_now, clause_words) *
                  has_permission(&lits)
             */
        }
    }


    return true;
}

/* Resolve backwards to one current-level literal (first UIP), then minimize
   the learned tail. The output certifies entailment and the asserting
   backjump shape. */
void solver_analyze(solver* s, clause* c, veci* learnt)
/*@ default */
{
    /*@ solver_analyze_pre(
          s, c, learnt, levels_ptr, anz_n, anz_F, anz_A_arr, K, M, anz_focus,
          C, anz_wl)
        which implies exists reasons_ptr trail_ptr tags_ptr,
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, M, anz_focus) &&
          propagation_conflict_cert(anz_n, anz_F, M, C) &&
          conflict_ptr_denotes(M, c, C) &&
          msolver_seed_shadow(M) &&
          ms_root_level(M) < Zlength(mt_lim(ms_core(M))) &&
          ms_tags(M) == repeat_Z(0, anz_n) &&
          ms_tagged(M) == nil && 2 * anz_n <= INT_MAX &&
          Zlength(z_nil) == 0 &&
          solver_rep_analyze_at(
            s, M, reasons_ptr, levels_ptr, trail_ptr, tags_ptr, anz_wl) *
          Veci::rep(learnt, z_nil)
     */
    /*@ Given reasons_ptr trail_ptr tags_ptr */
    /*@ analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, M, anz_focus) &&
        solver_rep_analyze_at(
          s, M, reasons_ptr, levels_ptr, trail_ptr, tags_ptr, anz_wl)
        which implies exists (activity_ptr orderpos_ptr : Z),
          solver_analyze_open_at(s, M, anz_n, activity_ptr, orderpos_ptr,
                  reasons_ptr, levels_ptr, trail_ptr, tags_ptr, anz_wl) *
          clause_db_rep(ms_prob(M)) *
          clause_db_rep(ms_learnt(M)) *
          binary_scratch_rep(ms_binary(M), ms_binary_lits(M))
     */
    lit*     trail   = s->trail;
    lbool*   tags    = s->tags;
    clause** reasons = s->reasons;
    int*     levels  = s->levels;
    int      cnt     = 0;
    lit      p       = lit_Undef;
    int      ind     = s->qtail-1;
    lit*     lits;
    int      i, j;
    unsigned int minl;
    int*     tagged;

    veci_push(learnt,lit_Undef);

    /*@ Veci::rep(learnt, app(z_nil, cons(-2, nil))) */
    /*@ Assert (exists (Mcur : msolver)
                          (phase : analyze_resolution_phase)
                          (Ccur : clause) (words : list Z),
          s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
          analysis_core_equiv(M, Mcur) &&
          msolver_seed_shadow(Mcur) &&
          c != 0 &&
          analyze_resolution_loop_inv(
            anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, phase, c, Ccur,
            words, cnt, ind, p) &&
          ms_root_level(Mcur) < Zlength(mt_lim(ms_core(Mcur))) &&
          2 * anz_n <= INT_MAX &&
          solver_rep_analyze_at(
            s, Mcur, reasons, levels, trail, tags, anz_wl) *
          Veci::rep(learnt, words) *
          has_permission(&lits) * has_permission(&i) *
          has_permission(&j) * has_permission(&minl) *
          has_permission(&tagged)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
     */
    do{
        /*@ exists (Mcur : msolver)
                              (phase : analyze_resolution_phase)
                              (Ccur : clause) (words : list Z)
                              reasons_loop trail_loop tags_loop,
              reasons == reasons_loop && trail == trail_loop &&
              tags == tags_loop &&
              analysis_core_equiv(M, Mcur) &&
              msolver_seed_shadow(Mcur) &&
              c != 0 &&
              analyze_resolution_loop_inv(
                anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, phase, c, Ccur,
                words, cnt, ind, p) &&
              ms_root_level(Mcur) < Zlength(mt_lim(ms_core(Mcur))) &&
              2 * anz_n <= INT_MAX &&
              solver_rep_analyze_at(
                s, Mcur, reasons, levels, trail, tags, anz_wl) *
              Veci::rep(learnt, words) *
              has_permission(&lits) * has_permission(&i) *
              has_permission(&j) * has_permission(&minl) *
              has_permission(&tagged)
         */
        /*@ Given Mcur phase Ccur words */
        /*@ ms_size(Mcur) == anz_n &&
            solver_rep_analyze_at(
              s, Mcur, reasons, levels, trail, tags, anz_wl)
            which implies exists (activity_ptr_loop orderpos_ptr_loop : Z),
              solver_shape(Mcur) && ms_size(Mcur) == anz_n &&
              solver_analyze_open_at(s, Mcur, anz_n, activity_ptr_loop, orderpos_ptr_loop,
                  reasons, levels, trail, tags, anz_wl) *
              clause_db_rep(ms_prob(Mcur)) *
              clause_db_rep(ms_learnt(Mcur)) *
              binary_scratch_rep(ms_binary(Mcur), ms_binary_lits(Mcur))
         */
        /*@ Given activity_ptr_loop orderpos_ptr_loop */
        assert(c != 0);

        if (clause_is_lit(c)){
            /*@ analyze_resolution_loop_inv(
                  anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, phase, c, Ccur,
                  words, cnt, ind, p) && is_tag(c) == msat_true
                which implies exists (S0 R0 : list Z)
                                     (learnt0 : clause) x,
                  analyze_resolution_loop_inv(
                    anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, phase, c, Ccur,
                    words, cnt, ind, p) &&
                  phase == AnalyzeSelected && In(x, S0) &&
                  cnt + 1 == Zlength(S0) && 0 < cnt &&
                  level_of(msolver_view(anz_n, Mcur), x) ==
                    Some(current_level(msolver_view(anz_n, Mcur))) &&
                  c == Znth(x, ms_reason_words(Mcur), 0) &&
                  reason_target_wf(anz_n, Mcur, x, c, Ccur) &&
                  analyze_inv(anz_F, msolver_view(anz_n, Mcur), S0, R0,
                              learnt0) &&
                  lits_denote(tl(words)) == learnt0 &&
                  Permutation(ms_tagged(Mcur),
                              analyze_tags(S0, R0, learnt0))
             */
            /*@ Given S0 R0 learnt0 x */
            lit q = clause_read_lit(c);
            /*@ analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus) &&
                  reason_target_wf(anz_n, Mcur, x, c, Ccur) &&
                  level_of(msolver_view(anz_n, Mcur), x) ==
                    Some(current_level(msolver_view(anz_n, Mcur))) &&
                  is_tag(c) == msat_true && q == tag_lit(c)
                which implies
                  reason_target_wf(anz_n, Mcur, x, c, Ccur) &&
                  analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus) &&
                  is_tag(c) == msat_true && q == tag_lit(c) &&
                  0 <= lit_var_c(q) && lit_var_c(q) < anz_n &&
                  level_of(msolver_view(anz_n, Mcur), lit_var_c(q)) ==
                    Some(current_level(msolver_view(anz_n, Mcur)))
             */
            assert(lit_var(q) /*@ where(original) */ >= 0 && lit_var(q) /*@ where(original) */ < s->size);
            /*@ CharArray::seg(tags, 0, anz_n, ms_tags(Mcur))
                which implies CharArray::full(tags, anz_n, ms_tags(Mcur))
             */
            if (tags[lit_var(q) /*@ where(original) */] == l_Undef && levels[lit_var(q) /*@ where(original) */] > 0){
                /*@ analyze_resolution_loop_inv(
                      anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, phase, c, Ccur,
                      words, cnt, ind, p) &&
                      0 <= lit_var_c(q) && lit_var_c(q) < anz_n &&
                      Znth(lit_var_c(q), ms_tags(Mcur), 0) == 0 &&
                      2 * anz_n <= INT_MAX
                    which implies
                      analyze_resolution_loop_inv(
                        anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, phase, c, Ccur,
                        words, cnt, ind, p) &&
                      0 <= lit_var_c(q) && lit_var_c(q) < anz_n &&
                      Znth(lit_var_c(q), ms_tags(Mcur), 0) == 0 &&
                      Zlength(ms_tagged(Mcur)) < anz_n &&
                      2 * anz_n <= INT_MAX
                 */
                tags[lit_var(q) /*@ where(original) */] = l_True;
                veci_push(&s->tagged,lit_var(q) /*@ where(original) */);
                act_var_bump(s,lit_var(q) /*@ where(original) */);
                /*@ exists (heap_now orderpos_now : list Z)
                           (activity_now : list fp64) var_inc_now,
                      order_heap_wf(anz_n, heap_now, orderpos_now) &&
                      Permutation(ms_order(Mcur), heap_now) &&
                      Zlength(activity_now) == anz_n &&
                      Zlength(orderpos_now) == anz_n &&
                      store(&(s->orderpos), int *, orderpos_ptr_loop) *
                      store(&(s->activity), double *, activity_ptr_loop) *
                      IntArray::seg(orderpos_ptr_loop, 0, anz_n, orderpos_now) *
                      DoubleArray::seg(activity_ptr_loop, 0, anz_n, activity_now) *
                      Veci::rep(&(s->order), heap_now) *
                      store(&(s->var_inc), double, var_inc_now)
                 */
                /*@ CharArray::full(
                      tags, anz_n,
                      replace_Znth(lit_var_c(q), 1, ms_tags(Mcur)))
                    which implies exists (tags_now : list Z),
                      tags_now ==
                        replace_Znth(lit_var_c(q), 1, ms_tags(Mcur)) &&
                      Zlength(tags_now) == anz_n &&
                      CharArray::full(tags, anz_n, tags_now)
                 */
                /*@ Given tags_now */
                /* binary_reason_same_level puts q at the selected variable's
                   current level, making this non-current branch unreachable. */
                /*@ analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus) &&
                      level_of(msolver_view(anz_n, Mcur), lit_var_c(q)) ==
                      Some(current_level(msolver_view(anz_n, Mcur)))
                    which implies
                      level_of(msolver_view(anz_n, Mcur), lit_var_c(q)) ==
                        Some(current_level(msolver_view(anz_n, Mcur))) &&
                      analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus) &&
                      mt_levels(ms_core(Mcur))[lit_var_c(q) - 0] ==
                        Zlength(mt_lim(ms_core(Mcur)))
                 */
                if (levels[lit_var(q) /*@ where(original) */] == solver_dlevel(s))
                    cnt++;
                else
                    /*@ Branch clear all */
                    veci_push(learnt,q);

            }
            /*@ Assert (exists (words1 : list Z)
                              (activity_j : list fp64)
                              (orderpos_j heap_j tags_j tagged_j : list Z)
                              var_inc_j
                              (Mtag : msolver) (S1 R1 : list Z)
                              (learnt1 : clause),
                  s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
                  Mtag == analyze_tag_step_msolver(
                            Mcur, tags_j, tagged_j,
                            activity_j, orderpos_j, heap_j, var_inc_j) &&
                  solver_shape(Mtag) && anz_n == ms_size(Mtag) &&
                  analysis_core_equiv(M, Mtag) &&
                  analysis_core_equiv(Mcur, Mtag) &&
                  msolver_seed_shadow(Mtag) &&
                  analyze_tagged_step(
                    anz_n, anz_F, anz_A_arr, K, Mcur, Mtag, anz_focus, c, q, Ccur,
                    S0, R0, learnt0, x, S1, R1, learnt1, words1, cnt) &&
                  analyze_backward_scan_inv(
                    anz_n, anz_F, anz_A_arr, K, Mtag, anz_focus, words1,
                    cnt, ind, S1, R1, learnt1) &&
                  0 <= lit_var_c(mt_trail(ms_core(Mtag))[ind - 0]) &&
                  lit_var_c(mt_trail(ms_core(Mtag))[ind - 0]) < anz_n &&
                  (ms_tags(Mtag)[
                     lit_var_c(mt_trail(ms_core(Mtag))[ind - 0]) - 0] == 0 =>
                   0 < ind) &&
                  0 <= ind && ind < ms_qtail(Mcur) &&
                  solver_analyze_open_at(s, Mtag, anz_n, activity_ptr_loop, orderpos_ptr_loop,
                  reasons, levels, trail, tags, anz_wl) *
                  clause_db_rep(ms_prob(Mcur)) *
                  clause_db_rep(ms_learnt(Mcur)) *
                  binary_scratch_rep(ms_binary(Mcur), ms_binary_lits(Mcur)) *
                  Veci::rep(learnt, words1) *
                  store(&p, lit, p) * has_permission(&lits) * has_permission(&i) *
                  has_permission(&j) * has_permission(&minl) * has_permission(&tagged)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
             */
            /*@ Given words1 activity_j orderpos_j heap_j tags_j
                      tagged_j var_inc_j
                      Mtag S1 R1 learnt1 */
            /*@ Mtag == analyze_tag_step_msolver(
                          Mcur, tags_j, tagged_j,
                          activity_j, orderpos_j, heap_j, var_inc_j) &&
                  solver_shape(Mtag) && anz_n == ms_size(Mtag) &&
                  analysis_core_equiv(M, Mtag) &&
                  analysis_core_equiv(Mcur, Mtag) &&
                  msolver_seed_shadow(Mtag) &&
                  analyze_tagged_step(
                    anz_n, anz_F, anz_A_arr, K, Mcur, Mtag, anz_focus, c, q, Ccur,
                    S0, R0, learnt0, x, S1, R1, learnt1, words1, cnt) &&
                  analyze_backward_scan_inv(
                    anz_n, anz_F, anz_A_arr, K, Mtag, anz_focus, words1,
                    cnt, ind, S1, R1, learnt1) &&
                  0 <= lit_var_c(mt_trail(ms_core(Mtag))[ind - 0]) &&
                  lit_var_c(mt_trail(ms_core(Mtag))[ind - 0]) < anz_n &&
                  (ms_tags(Mtag)[
                     lit_var_c(mt_trail(ms_core(Mtag))[ind - 0]) - 0] == 0 =>
                   0 < ind) &&
                  0 <= ind && ind < ms_qtail(Mcur) &&
                  solver_analyze_open_at(s, Mtag, anz_n, activity_ptr_loop, orderpos_ptr_loop,
                  reasons, levels, trail, tags, anz_wl) *
                  clause_db_rep(ms_prob(Mcur)) *
                  clause_db_rep(ms_learnt(Mcur)) *
                  binary_scratch_rep(ms_binary(Mcur), ms_binary_lits(Mcur)) *
                  Veci::rep(learnt, words1)
                which implies
                  analysis_core_equiv(M, Mtag) &&
                  analysis_core_equiv(Mcur, Mtag) &&
                  msolver_seed_shadow(Mtag) &&
                  0 <= ind && ind < ms_qtail(Mtag) &&
                  analyze_tagged_step(
                    anz_n, anz_F, anz_A_arr, K, Mcur, Mtag, anz_focus, c, q, Ccur,
                    S0, R0, learnt0, x, S1, R1, learnt1, words1, cnt) &&
                  analyze_backward_scan_inv(
                    anz_n, anz_F, anz_A_arr, K, Mtag, anz_focus, words1,
                    cnt, ind, S1, R1, learnt1) &&
                  0 <= lit_var_c(mt_trail(ms_core(Mtag))[ind - 0]) &&
                  lit_var_c(mt_trail(ms_core(Mtag))[ind - 0]) < anz_n &&
                  (ms_tags(Mtag)[
                     lit_var_c(mt_trail(ms_core(Mtag))[ind - 0]) - 0] == 0 =>
                   0 < ind) &&
                  solver_rep_analyze_at(
                    s, Mtag, reasons, levels, trail, tags, anz_wl) *
                  Veci::rep(learnt, words1)
             */
        }else{

            /*@ analyze_resolution_loop_inv(
                  anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, phase, c, Ccur,
                  words, cnt, ind, p) && is_tag(c) == msat_false && 0 < c &&
                  clause_db_rep(ms_prob(Mcur)) *
                  clause_db_rep(ms_learnt(Mcur)) *
                  binary_scratch_rep(ms_binary(Mcur), ms_binary_lits(Mcur))
                which implies exists (is_learnt_now : bool)
                                     (clause_words : list Z),
                  analyze_resolution_loop_inv(
                    anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, phase, c, Ccur,
                    words, cnt, ind, p) && 0 < c &&
                  Ccur == lits_denote(clause_words) &&
                  Forall(lit_wf_c(anz_n), clause_words) &&
                  store(clause_hdr_addr(c), int,
                        clause_hdr_word(is_learnt_now,
                                        Zlength(clause_words))) *
                  activity_state(c, is_learnt_now, Zlength(clause_words)) *
                  IntArray::seg(clause_lits_addr(c), 0,
                                Zlength(clause_words), clause_words) *
                  analysis_clause_remainder(
                    Mcur, c, is_learnt_now, clause_words)
             */
            /*@ Given is_learnt_now clause_words */

            if (clause_learnt(c))
                /*@ is_learnt_now == msat_true &&
                      is_tag(c) == msat_false && 0 < c &&
                      In(c, db_words(ms_learnt(Mcur))) &&
                      msat_fp32_nonnegative(ms_cla_inc(Mcur)) &&
                      store(clause_hdr_addr(c), int,
                            clause_hdr_word(is_learnt_now,
                                            Zlength(clause_words))) *
                      activity_state(c, is_learnt_now, Zlength(clause_words)) *
                      IntArray::seg(clause_lits_addr(c), 0,
                                    Zlength(clause_words), clause_words) *
                      analysis_clause_remainder(
                        Mcur, c, is_learnt_now, clause_words)
                    which implies
                      is_tag(c) == msat_false &&
                      0 < c && In(c, db_words(ms_learnt(Mcur))) &&
                      msat_fp32_nonnegative(ms_cla_inc(Mcur)) &&
                      clause_db_rep(ms_prob(Mcur)) *
                      clause_db_rep(ms_learnt(Mcur)) *
                      binary_scratch_rep(ms_binary(Mcur), ms_binary_lits(Mcur))
                 */
                /*@ Branch name learnt */
                act_clause_bump(s,c);

            /*@ is_tag(c) == msat_false && 0 < c &&
                  store(clause_hdr_addr(c), int,
                      clause_hdr_word(is_learnt_now,
                                      Zlength(clause_words))) *
                  activity_state(c, is_learnt_now, Zlength(clause_words)) *
                  IntArray::seg(clause_lits_addr(c), 0,
                                Zlength(clause_words), clause_words) *
                  analysis_clause_remainder(
                    Mcur, c, is_learnt_now, clause_words)
                $ unnamed
                which implies
                  is_tag(c) == msat_false &&
                  0 < c &&
                  clause_db_rep(ms_prob(Mcur)) *
                  clause_db_rep(ms_learnt(Mcur)) *
                  binary_scratch_rep(ms_binary(Mcur), ms_binary_lits(Mcur))
             */

            /*@ Assert (exists (Mact : msolver),
                  s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
                  analysis_core_equiv(M, Mact) &&
                  analysis_core_equiv(Mcur, Mact) &&
                  msolver_seed_shadow(Mact) &&
                  2 * anz_n <= INT_MAX &&
                  is_tag(c) == msat_false &&
                  analyze_resolution_loop_inv(
                    anz_n, anz_F, anz_A_arr, K, Mact, anz_focus, phase, c, Ccur,
                    words, cnt, ind, p) &&
                  ms_qtail(Mact) == ms_qtail(Mcur) &&
                  ms_cap(Mact) == ms_cap(Mcur) &&
                  solver_analyze_open_at(s, Mact, anz_n, activity_ptr_loop, orderpos_ptr_loop,
                  reasons, levels, trail, tags, anz_wl) *
                  clause_db_rep(ms_prob(Mact)) *
                  clause_db_rep(ms_learnt(Mact)) *
                  binary_scratch_rep(ms_binary(Mact), ms_binary_lits(Mact)) *
                  Veci::rep(learnt, words) *
                  has_permission(&lits) * has_permission(&i) * has_permission(&j) *
                  has_permission(&minl) * has_permission(&tagged)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
             */
            /*@ Given Mact */
            /*@ solver_analyze_open_at(s, Mact, anz_n, activity_ptr_loop, orderpos_ptr_loop,
                  reasons, levels, trail, tags, anz_wl) *
                clause_db_rep(ms_prob(Mact)) *
                clause_db_rep(ms_learnt(Mact)) *
                binary_scratch_rep(ms_binary(Mact), ms_binary_lits(Mact)) &&
                  msolver_seed_shadow(Mact) && 2 * anz_n <= INT_MAX &&
                  is_tag(c) == msat_false &&
                  analyze_resolution_loop_inv(
                    anz_n, anz_F, anz_A_arr, K, Mact, anz_focus, phase, c, Ccur,
                    words, cnt, ind, p)
                which implies exists (activity_ptr_clause orderpos_ptr_clause : Z)
                                     (is_learnt2 : bool) (clause_words2 : list Z),
                  msolver_seed_shadow(Mact) && 2 * anz_n <= INT_MAX &&
                  analyze_resolution_loop_inv(
                    anz_n, anz_F, anz_A_arr, K, Mact, anz_focus, phase, c, Ccur,
                    words, cnt, ind, p) &&
                  is_tag(c) == msat_false &&
                  Ccur == lits_denote(clause_words2) &&
                  Forall(lit_wf_c(anz_n), clause_words2) &&
                  solver_analyze_open_at(s, Mact, anz_n, activity_ptr_clause, orderpos_ptr_clause,
                  reasons, levels, trail, tags, anz_wl) *
                  store(clause_hdr_addr(c), int, clause_hdr_word(is_learnt2, Zlength(clause_words2))) *
                  activity_state(c, is_learnt2, Zlength(clause_words2)) *
                  IntArray::seg(clause_lits_addr(c), 0, Zlength(clause_words2), clause_words2) *
                  analysis_clause_remainder( Mact, c, is_learnt2, clause_words2)
             */
            /*@ Given activity_ptr_clause orderpos_ptr_clause
                      is_learnt2 clause_words2 */

            lits = clause_begin(c);
            //printlits(lits,lits+clause_size(c)); printf("\n");
            /*@ Inv Assert (exists (Mscan : msolver) (S0 R0 : list Z)
                                  (learnt0 : clause) x
                                  (Sscan Rscan : list Z)
                                  (learnt_scan : clause)
                                  (words_scan : list Z)
                                  (activity_ptr_scan orderpos_ptr_scan : Z),
                  s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
                  analysis_core_equiv(Mact, Mscan) &&
                  analysis_core_equiv(M, Mscan) &&
                  msolver_seed_shadow(Mscan) &&
                  2 * anz_n <= INT_MAX &&
                  analyze_clause_scan_inv(
                    anz_n, anz_F, anz_A_arr, K, Mact, Mscan, anz_focus, phase, Ccur, j, ind,
                    S0, R0, learnt0, x, Sscan, Rscan, learnt_scan,
                    words_scan, cnt) &&
                  ((phase == AnalyzeInitial && j == 0 && Mscan == Mact) ||
                   (phase == AnalyzeInitial && 0 < j) ||
                   (phase == AnalyzeSelected && j == 1 && Mscan == Mact) ||
                   (phase == AnalyzeSelected && 1 < j)) &&
                  Ccur == lits_denote(clause_words2) &&
                  lits == clause_lits_addr(c) &&
                  clause_lits_pointer(c, lits) &&
                  clause_hdr_word(is_learnt2,
                    Zlength(clause_words2)) / 2 == Zlength(clause_words2) &&
                  0 <= ind && ind < ms_qtail(Mscan) &&
                  0 <= j && j <= Zlength(clause_words2) &&
                  Forall(lit_wf_c(anz_n), clause_words2) &&
                  solver_analyze_open_at(s, Mscan, anz_n, activity_ptr_scan, orderpos_ptr_scan,
                  reasons, levels, trail, tags, anz_wl) *
                  Veci::rep(learnt, words_scan) *
                  store(clause_hdr_addr(c), int, clause_hdr_word(is_learnt2, Zlength(clause_words2))) *
                  activity_state(c, is_learnt2, Zlength(clause_words2)) *
                  IntArray::seg(lits, 0, Zlength(clause_words2), clause_words2) *
                  analysis_clause_remainder( Mscan, c, is_learnt2, clause_words2) *
                  store(&p, lit, p) *
                  has_permission(&i) *
                  has_permission(&minl) *
                  has_permission(&tagged)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
             */
            for (j = (p == lit_Undef ? 0 : 1); j < clause_size(c); j++){
                /*@ Given Mscan S0 R0 learnt0 x Sscan Rscan learnt_scan words_scan */
                lit q = lits[j];
                /*@ Forall(lit_wf_c(anz_n), clause_words2) &&
                      0 <= j && j < Zlength(clause_words2) &&
                      q == clause_words2[j - 0]
                    which implies
                      Forall(lit_wf_c(anz_n), clause_words2) &&
                      0 <= j && j < Zlength(clause_words2) &&
                      q == clause_words2[j - 0] &&
                      0 <= lit_var_c(q) && lit_var_c(q) < anz_n
                 */
                assert(lit_var(q) /*@ where(original) */ >= 0 && lit_var(q) /*@ where(original) */ < s->size);
                if (tags[lit_var(q) /*@ where(original) */] == l_Undef && levels[lit_var(q) /*@ where(original) */] > 0){
                    /*@ analyze_clause_scan_inv(
                          anz_n, anz_F, anz_A_arr, K, Mact, Mscan, anz_focus, phase, Ccur, j, ind,
                          S0, R0, learnt0, x, Sscan, Rscan, learnt_scan,
                          words_scan, cnt) &&
                          0 <= lit_var_c(q) && lit_var_c(q) < anz_n &&
                          Znth(lit_var_c(q), ms_tags(Mscan), 0) == 0 &&
                          2 * anz_n <= INT_MAX
                        which implies
                          analyze_clause_scan_inv(
                            anz_n, anz_F, anz_A_arr, K, Mact, Mscan, anz_focus, phase,
                            Ccur, j, ind, S0, R0, learnt0, x, Sscan, Rscan,
                            learnt_scan, words_scan, cnt) &&
                          0 <= lit_var_c(q) && lit_var_c(q) < anz_n &&
                          Znth(lit_var_c(q), ms_tags(Mscan), 0) == 0 &&
                          Zlength(ms_tagged(Mscan)) < anz_n &&
                          Zlength(words_scan) <= anz_n &&
                          2 * anz_n <= INT_MAX
                     */
                    tags[lit_var(q) /*@ where(original) */] = l_True;
                    veci_push(&s->tagged,lit_var(q) /*@ where(original) */);
                    act_var_bump(s,lit_var(q) /*@ where(original) */);
                    if (levels[lit_var(q) /*@ where(original) */] == solver_dlevel(s))
                        cnt++;
                    else
                        veci_push(learnt,q);
                }
            }
            /*@ exists (Mdone : msolver) (Sdone Rdone : list Z)
                       (learnt_done : clause)
                       (activity_ptr_done orderpos_ptr_done : Z)
                       (words_done : list Z),
                  analysis_core_equiv(M, Mdone) &&
                  msolver_seed_shadow(Mdone) &&
                  analyze_backward_scan_inv(
                    anz_n, anz_F, anz_A_arr, K, Mdone, anz_focus, words_done,
                    cnt, ind, Sdone, Rdone, learnt_done) &&
                  0 <= lit_var_c(mt_trail(ms_core(Mdone))[ind - 0]) &&
                  lit_var_c(mt_trail(ms_core(Mdone))[ind - 0]) < anz_n &&
                  (ms_tags(Mdone)[
                     lit_var_c(mt_trail(ms_core(Mdone))[ind - 0]) - 0] == 0 =>
                   0 < ind) &&
                  clause_lits_pointer(c, lits) &&
                  store(&j, int, j) *
                  solver_analyze_open_at(s, Mdone, anz_n, activity_ptr_done, orderpos_ptr_done,
                  reasons, levels, trail, tags, anz_wl) *
                  store(clause_hdr_addr(c), int,
                        clause_hdr_word(is_learnt2,
                                        Zlength(clause_words2))) *
                  activity_state(c, is_learnt2, Zlength(clause_words2)) *
                  IntArray::seg(lits, 0,
                                Zlength(clause_words2), clause_words2) *
                  analysis_clause_remainder(
                    Mdone, c, is_learnt2, clause_words2) *
                  Veci::rep(learnt, words_done)
             */
            /*@ Given Mdone Sdone Rdone learnt_done
                      activity_ptr_done orderpos_ptr_done
                      words_done */
            /*@ analysis_core_equiv(M, Mdone) &&
                  msolver_seed_shadow(Mdone) &&
                  analyze_backward_scan_inv(
                    anz_n, anz_F, anz_A_arr, K, Mdone, anz_focus, words_done,
                    cnt, ind, Sdone, Rdone, learnt_done) &&
                  0 <= lit_var_c(mt_trail(ms_core(Mdone))[ind - 0]) &&
                  lit_var_c(mt_trail(ms_core(Mdone))[ind - 0]) < anz_n &&
                  (ms_tags(Mdone)[
                     lit_var_c(mt_trail(ms_core(Mdone))[ind - 0]) - 0] == 0 =>
                   0 < ind) &&
                  clause_lits_pointer(c, lits) &&
                  store(&j, int, j) *
                  solver_analyze_open_at(s, Mdone, anz_n, activity_ptr_done, orderpos_ptr_done,
                  reasons, levels, trail, tags, anz_wl) *
                  store(clause_hdr_addr(c), int,
                        clause_hdr_word(is_learnt2,
                                        Zlength(clause_words2))) *
                  activity_state(c, is_learnt2, Zlength(clause_words2)) *
                  IntArray::seg(lits, 0,
                                Zlength(clause_words2), clause_words2) *
                  analysis_clause_remainder(
                    Mdone, c, is_learnt2, clause_words2) *
                  Veci::rep(learnt, words_done)
                which implies
                  analysis_core_equiv(M, Mdone) &&
                  msolver_seed_shadow(Mdone) &&
                  analyze_backward_scan_inv(
                    anz_n, anz_F, anz_A_arr, K, Mdone, anz_focus, words_done,
                    cnt, ind, Sdone, Rdone, learnt_done) &&
                  0 <= ind && ind < ms_qtail(Mdone) &&
                  0 <= lit_var_c(mt_trail(ms_core(Mdone))[ind - 0]) &&
                  lit_var_c(mt_trail(ms_core(Mdone))[ind - 0]) < anz_n &&
                  (ms_tags(Mdone)[
                     lit_var_c(mt_trail(ms_core(Mdone))[ind - 0]) - 0] == 0 =>
                   0 < ind) &&
                  clause_lits_pointer(c, lits) &&
                  has_permission(&j) *
                  solver_rep_analyze_at(
                    s, Mdone, reasons, levels, trail, tags, anz_wl) *
                  Veci::rep(learnt, words_done)
             */
        }

        /*@ Branch join all with Assert (exists (Mresolved : msolver) (Sresolved Rresolved : list Z)
                          (learnt_resolved : clause)
                          (words_resolved : list Z),
              s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
              analysis_core_equiv(M, Mresolved) &&
              msolver_seed_shadow(Mresolved) &&
              analyze_backward_scan_inv(
                anz_n, anz_F, anz_A_arr, K, Mresolved, anz_focus, words_resolved,
                cnt, ind, Sresolved, Rresolved, learnt_resolved) &&
              0 <= ind && ind < ms_qtail(Mresolved) &&
              0 <= lit_var_c(
                     mt_trail(ms_core(Mresolved))[ind - 0]) &&
              lit_var_c(mt_trail(ms_core(Mresolved))[ind - 0]) < anz_n &&
              (ms_tags(Mresolved)[
                 lit_var_c(mt_trail(ms_core(Mresolved))[ind - 0]) - 0] == 0 =>
               0 < ind) &&
              solver_rep_analyze_at(
                s, Mresolved, reasons, levels, trail, tags, anz_wl) *
              Veci::rep(learnt, words_resolved) *
              store(&p, lit, p) *
              store(&c, clause *, c) *
              has_permission(&lits) * has_permission(&i) *
              has_permission(&j) * has_permission(&minl) *
              has_permission(&tagged)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
         */
        /*@ Given Mresolved Sresolved Rresolved learnt_resolved
                  words_resolved */
        /*@ ms_size(Mresolved) == anz_n &&
            solver_rep_analyze_at(
              s, Mresolved, reasons, levels, trail, tags, anz_wl)
            which implies exists (activity_ptr_back orderpos_ptr_back : Z),
              solver_analyze_open_at(s, Mresolved, anz_n, activity_ptr_back, orderpos_ptr_back,
                  reasons, levels, trail, tags, anz_wl) *
              clause_db_rep(ms_prob(Mresolved)) *
              clause_db_rep(ms_learnt(Mresolved)) *
              binary_scratch_rep(ms_binary(Mresolved), ms_binary_lits(Mresolved))
         */
        /*@ Given activity_ptr_back orderpos_ptr_back */

        /*@ Inv Assert (s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
              analysis_core_equiv(M, Mresolved) &&
              msolver_seed_shadow(Mresolved) &&
              analyze_backward_scan_inv(
                anz_n, anz_F, anz_A_arr, K, Mresolved, anz_focus, words_resolved,
                cnt, ind, Sresolved, Rresolved, learnt_resolved) &&
              0 <= ind && ind < ms_qtail(Mresolved) &&
              0 <= lit_var_c(
                     mt_trail(ms_core(Mresolved))[ind - 0]) &&
              lit_var_c(mt_trail(ms_core(Mresolved))[ind - 0]) < anz_n &&
              (ms_tags(Mresolved)[
                 lit_var_c(mt_trail(ms_core(Mresolved))[ind - 0]) - 0] == 0 =>
               0 < ind) &&
              solver_analyze_open_at(s, Mresolved, anz_n, activity_ptr_back, orderpos_ptr_back,
                  reasons, levels, trail, tags, anz_wl) *
              Veci::rep(learnt, words_resolved) *
              clause_db_rep(ms_prob(Mresolved)) *
              clause_db_rep(ms_learnt(Mresolved)) *
              binary_scratch_rep(ms_binary(Mresolved), ms_binary_lits(Mresolved)) *
              has_permission(&c) * has_permission(&p) *
              has_permission(&lits) * has_permission(&i) *
              has_permission(&j) * has_permission(&minl) *
              has_permission(&tagged)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
         */
        while (tags[lit_var(trail[ind]) /*@ where(original) */] == l_Undef)
            ind--;
        ind--;

        p = trail[ind+1];
        /*@ 0 <= lit_var_c(mt_trail(ms_core(Mresolved))[ind + 1 - 0]) &&
              lit_var_c(mt_trail(ms_core(Mresolved))[ind + 1 - 0]) < anz_n &&
              p == mt_trail(ms_core(Mresolved))[ind + 1 - 0]
            which implies
              0 <= lit_var_c(mt_trail(ms_core(Mresolved))[ind + 1 - 0]) &&
              lit_var_c(mt_trail(ms_core(Mresolved))[ind + 1 - 0]) < anz_n &&
              p == mt_trail(ms_core(Mresolved))[ind + 1 - 0] &&
              0 <= lit_var_c(p) && lit_var_c(p) < anz_n
         */
        c = reasons[lit_var(p) /*@ where(original) */];
        cnt--;

        /*@ Branch join all with Assert (s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
              analysis_core_equiv(M, Mresolved) &&
              msolver_seed_shadow(Mresolved) &&
              ((cnt == 0 && exists c_exit ind_exit,
                c == c_exit && ind == ind_exit &&
                analyze_resolution_exit(
                  anz_n, anz_F, anz_A_arr, K, Mresolved, anz_focus, p,
                  words_resolved)) ||
               (cnt > 0 && c != 0 && exists (Cnext : clause),
                reason_target_wf(
                  anz_n, Mresolved, lit_var_c(p), c, Cnext) &&
                  analyze_resolution_loop_inv(
                    anz_n, anz_F, anz_A_arr, K, Mresolved, anz_focus, AnalyzeSelected,
                    c, Cnext, words_resolved, cnt, ind, p))) &&
              ms_root_level(Mresolved) <
                Zlength(mt_lim(ms_core(Mresolved))) &&
              2 * anz_n <= INT_MAX &&
              solver_rep_analyze_at(
                s, Mresolved, reasons, levels, trail, tags, anz_wl) *
              Veci::rep(learnt, words_resolved) *
              has_permission(&lits) * has_permission(&i) *
              has_permission(&j) * has_permission(&minl) *
              has_permission(&tagged)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
         */

    } /*@ Inv Assert (exists (Mcur : msolver)
                          (phase : analyze_resolution_phase)
                          (Ccur : clause) (words : list Z),
          s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
          analysis_core_equiv(M, Mcur) &&
          msolver_seed_shadow(Mcur) &&
          ((cnt == 0 && exists c_exit ind_exit,
            c == c_exit && ind == ind_exit &&
            analyze_resolution_exit(
              anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, p, words)) ||
           (cnt > 0 && c != 0 &&
            analyze_resolution_loop_inv(
              anz_n, anz_F, anz_A_arr, K, Mcur, anz_focus, phase, c, Ccur,
              words, cnt, ind, p))) &&
          ms_root_level(Mcur) < Zlength(mt_lim(ms_core(Mcur))) &&
          2 * anz_n <= INT_MAX &&
          solver_rep_analyze_at(
            s, Mcur, reasons, levels, trail, tags, anz_wl) *
          Veci::rep(learnt, words) *
          has_permission(&lits) * has_permission(&i) *
          has_permission(&j) * has_permission(&minl) *
          has_permission(&tagged)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
     */
    while (cnt > 0);

    /*@ exists (Mresolution : msolver) (words_before : list Z),
          analysis_core_equiv(M, Mresolution) &&
          msolver_seed_shadow(Mresolution) &&
          analyze_resolution_exit(
            anz_n, anz_F, anz_A_arr, K, Mresolution, anz_focus, p, words_before) &&
          cnt == 0 &&
          solver_rep_analyze_at(
            s, Mresolution, reasons, levels, trail, tags, anz_wl) *
          Veci::rep(learnt, words_before)
     */
    /*@ Given Mresolution words_before */
    /*@ analyze_resolution_exit(
          anz_n, anz_F, anz_A_arr, K, Mresolution, anz_focus, p, words_before)
        which implies
          analyze_resolution_exit(
            anz_n, anz_F, anz_A_arr, K, Mresolution, anz_focus, p, words_before) &&
          1 <= Zlength(words_before) && Zlength(words_before) <= anz_n
     */
    /*@ exists learnt_ptr_uip,
          1 <= Zlength(words_before) &&
          Veci::rep_ptr(learnt, learnt_ptr_uip, words_before)
     */
    /*@ Given learnt_ptr_uip */
    *veci_begin(learnt) = lit_neg(p) /*@ where (original) */;
    /*@ 1 <= Zlength(words_before) &&
          IntArray::missing_i(learnt_ptr_uip, 0, 0,
                              Zlength(words_before), words_before) *
          store(learnt_ptr_uip, int, lit_neg_c(p))
        which implies
          IntArray::seg(learnt_ptr_uip, 0, Zlength(words_before),
                        replace_Znth(0, lit_neg_c(p), words_before))
     */

    /*@ exists (words_uip : list Z),
          words_uip == replace_Znth(0, lit_neg_c(p), words_before) &&
          analysis_core_equiv(M, Mresolution) &&
          msolver_seed_shadow(Mresolution) &&
          analysis_cancel_ready(
            anz_n, anz_F, anz_A_arr, K, Mresolution, anz_focus) &&
          1 <= Zlength(words_uip) && Zlength(words_uip) <= anz_n &&
          Forall(lit_wf_c(anz_n), words_uip) &&
          NoDup(map(lit_var_c, words_uip)) &&
          analyze_clause_cert(anz_n, anz_F, Mresolution, words_uip) &&
          analysis_tags_exact(
            anz_n, ms_tags(Mresolution), ms_tagged(Mresolution)) &&
          incl(map(lit_var_c, words_uip), ms_tagged(Mresolution)) &&
          minimize_tag_scope(
            anz_n, Mresolution, words_uip, nil) &&
          Veci::rep_ptr(learnt, learnt_ptr_uip, words_uip)
     */
    /*@ Given words_uip */

    lits = veci_begin(learnt);
    /*@ 2 * anz_n <= INT_MAX && anz_n == ms_size(Mresolution) &&
        solver_rep_analyze_at(
          s, Mresolution, reasons, levels, trail, tags, anz_wl)
        which implies
        solver_shape(Mresolution) &&
        2 * anz_n <= INT_MAX &&
        anz_n == ms_size(Mresolution) &&
        store(&(s->reasons), reasons) *
        PtrArray::seg(reasons, 0, anz_n, ms_reason_words(Mresolution)) *
        solver_ptr_tail(reasons, anz_n, ms_cap(Mresolution)) *
        store(&(s->levels), levels) *
        IntArray::seg(levels, 0, anz_n, mt_levels(ms_core(Mresolution))) *
        solver_int_tail(levels, anz_n, ms_cap(Mresolution)) *
        solver_reason_levels_frame_at(s, Mresolution, trail, tags, anz_wl)
     */
    minl = 0;
    /*@ Inv Assert (s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
          solver_shape(Mresolution) &&
          2 * anz_n <= INT_MAX &&
          0 <= minl && minl <= UINT_MAX &&
          1 <= i && i <= Zlength(words_uip) &&
          Forall(lit_wf_c(anz_n), words_uip) &&
          analysis_core_equiv(M, Mresolution) &&
          msolver_seed_shadow(Mresolution) &&
          analysis_cancel_ready(
            anz_n, anz_F, anz_A_arr, K, Mresolution, anz_focus) &&
          analysis_tags_exact(
            anz_n, ms_tags(Mresolution), ms_tagged(Mresolution)) &&
          analyze_clause_cert(anz_n, anz_F, Mresolution, words_uip) &&
          incl(map(lit_var_c, words_uip), ms_tagged(Mresolution)) &&
          minimize_tag_scope(
            anz_n, Mresolution, words_uip, nil) &&
          store(&(s->reasons), reasons) *
          PtrArray::seg(reasons, 0, anz_n, ms_reason_words(Mresolution)) *
          solver_ptr_tail(reasons, anz_n, ms_cap(Mresolution)) *
          store(&(s->levels), levels) *
          IntArray::seg(levels, 0, anz_n, mt_levels(ms_core(Mresolution))) *
          solver_int_tail(levels, anz_n, ms_cap(Mresolution)) *
          solver_reason_levels_frame_at(s, Mresolution, trail, tags, anz_wl) *
          Veci::rep_ptr(learnt, lits, words_uip) *
          has_permission(&c) * has_permission(&cnt) *
          has_permission(&p) * has_permission(&ind) *
          has_permission(&j) *
          has_permission(&tagged)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
     */
    for (i = 1; i < veci_size(learnt); i++){
        /*@ Forall(lit_wf_c(anz_n), words_uip) &&
              0 <= i && i < Zlength(words_uip)
            which implies
              Forall(lit_wf_c(anz_n), words_uip) &&
              0 <= i && i < Zlength(words_uip) &&
              0 <= lit_var_c(words_uip[i - 0]) &&
              lit_var_c(words_uip[i - 0]) < anz_n
         */
        int lev = levels[lit_var(lits[i]) /*@ where(original) */];
        minl    |= 1U << (lev & 31);
    }

    // simplify (full)
    j = 1;
    /*@ Inv Assert (exists (Mmin : msolver) (kept removed T : list Z)
                          (words_min : list Z) minl_v,
          s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
          analysis_core_equiv(M, Mmin) &&
          solver_shape(Mmin) &&
          2 * anz_n <= INT_MAX &&
          analysis_tags_exact(anz_n, ms_tags(Mmin), ms_tagged(Mmin)) &&
          msolver_seed_shadow(Mmin) &&
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mmin, anz_focus) &&
          analyze_clause_cert(anz_n, anz_F, Mmin, words_uip) &&
          analyze_minimize_loop_inv(
            anz_n, Mmin, words_uip, kept, removed, words_min, T, i, j) &&
          1 <= j && j <= i && i <= Zlength(words_min) &&
          Forall(lit_wf_c(anz_n), words_uip) &&
          Forall(lit_wf_c(anz_n), words_min) &&
          incl(map(lit_var_c, words_min),
               map(lit_var_c, mt_trail(ms_core(Mmin)))) &&
          incl(map(lit_var_c, words_min), ms_tagged(Mmin)) &&
          0 <= minl_v && minl_v <= UINT_MAX &&
          solver_rep_analyze_at(
            s, Mmin, reasons, levels, trail, tags, anz_wl) *
          Veci::rep_ptr(learnt, lits, words_min) *
          has_permission(&c) * has_permission(&cnt) *
          has_permission(&p) * has_permission(&ind) *
          store(&minl, unsigned int, minl_v) *
          has_permission(&tagged)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
     */
    for (i = 1; i < veci_size(learnt); i++){
        /*@ Given Mmin kept removed T words_min */
        /*@ solver_shape(Mmin) &&
            analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mmin, anz_focus) &&
            solver_rep_analyze_at(
              s, Mmin, reasons, levels, trail, tags, anz_wl)
            which implies
            store(&(s->reasons), reasons) *
            PtrArray::seg(reasons, 0, anz_n, ms_reason_words(Mmin)) *
            solver_ptr_tail(reasons, anz_n, ms_cap(Mmin)) *
            store(&(s->levels), levels) *
            IntArray::seg(levels, 0, anz_n, mt_levels(ms_core(Mmin))) *
            solver_int_tail(levels, anz_n, ms_cap(Mmin)) *
            solver_reason_levels_frame_at(s, Mmin, trail, tags, anz_wl)
         */
        /*@ Forall(lit_wf_c(anz_n), words_min) &&
              0 <= i && i < Zlength(words_min)
            which implies
              Forall(lit_wf_c(anz_n), words_min) &&
              0 <= i && i < Zlength(words_min) &&
              0 <= lit_var_c(words_min[i - 0]) &&
              lit_var_c(words_min[i - 0]) < anz_n
         */
        if (reasons[lit_var(lits[i]) /*@ where(original) */] == 0 ||
            !solver_lit_removable(s,lits[i],minl)
              /*@ where reasons_ptr = reasons, levels_ptr = levels,
                        trail_ptr = trail, tags_ptr = tags,
                        lrm_n = anz_n, lrm_F = anz_F, lrm_A_arr = anz_A_arr, lrm_K = K,
                        M = Mmin, lrm_focus = anz_focus, lrm_wl = anz_wl */) {
            lits[j] = lits[i];
            j++;
        }
    }

    // update size of learnt + statistics
    /*@ exists (Mmin_done : msolver) (kept_done removed_done T_done : list Z)
                      (words_done : list Z),
          analysis_core_equiv(M, Mmin_done) &&
          msolver_seed_shadow(Mmin_done) &&
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mmin_done, anz_focus) &&
          analysis_tags_exact(anz_n, ms_tags(Mmin_done), ms_tagged(Mmin_done)) &&
          analyze_clause_cert(anz_n, anz_F, Mmin_done, words_uip) &&
          analyze_minimize_loop_inv(
            anz_n, Mmin_done, words_uip, kept_done, removed_done,
            words_done, T_done, i, j) &&
          solver_rep_analyze_at(
            s, Mmin_done, reasons, levels, trail, tags, anz_wl) *
          Veci::rep_ptr(learnt, lits, words_done)
     */
    /*@ Given Mmin_done kept_done removed_done T_done words_done */
    /*@ solver_rep_analyze_at(
          s, Mmin_done, reasons, levels, trail, tags, anz_wl)
        which implies
          store(&(s->stats.max_literals),
                stats_max_literals(ms_stats(Mmin_done))) *
          store(&(s->stats.tot_literals),
                stats_tot_literals(ms_stats(Mmin_done))) *
          solver_literal_stats_frame_at(
            s, Mmin_done, reasons, levels, trail, tags, anz_wl)
     */
    s->stats.max_literals += veci_size(learnt);
    veci_resize(learnt,j);
    s->stats.tot_literals += j;

    /*@ exists max_lits tot_lits,
          store(&(s->stats.max_literals), max_lits) *
          store(&(s->stats.tot_literals), tot_lits) *
          solver_literal_stats_frame_at(
            s, Mmin_done, reasons, levels, trail, tags, anz_wl)
     */
    /*@ Given max_lits tot_lits */
    /*@ analysis_core_equiv(M, Mmin_done) &&
          msolver_seed_shadow(Mmin_done) &&
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mmin_done, anz_focus) &&
          analysis_tags_exact(anz_n, ms_tags(Mmin_done), ms_tagged(Mmin_done)) &&
          analyze_clause_cert(anz_n, anz_F, Mmin_done, words_uip) &&
          analyze_minimize_loop_inv(
            anz_n, Mmin_done, words_uip, kept_done, removed_done,
            words_done, T_done, i, j) &&
          store(&(s->stats.max_literals), max_lits) *
          store(&(s->stats.tot_literals), tot_lits) *
          solver_literal_stats_frame_at(
            s, Mmin_done, reasons, levels, trail, tags, anz_wl)
        which implies exists (Mstats_upd : msolver),
          analysis_core_equiv(M, Mstats_upd) &&
          msolver_seed_shadow(Mstats_upd) &&
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mstats_upd, anz_focus) &&
          analysis_tags_exact(anz_n, ms_tags(Mstats_upd), ms_tagged(Mstats_upd)) &&
          analyze_clause_cert(anz_n, anz_F, Mstats_upd, words_uip) &&
          analyze_minimize_loop_inv(
            anz_n, Mstats_upd, words_uip, kept_done, removed_done,
            words_done, T_done, i, j) &&
          solver_rep_analyze_at(
            s, Mstats_upd, reasons, levels, trail, tags, anz_wl)
     */

    /*@ exists (Mstats : msolver) (words_compact : list Z),
          analysis_core_equiv(M, Mstats) &&
          msolver_seed_shadow(Mstats) &&
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mstats, anz_focus) &&
          words_compact == sublist(0, j, words_done) &&
          1 <= Zlength(words_compact) && Zlength(words_compact) <= anz_n &&
          Forall(lit_wf_c(anz_n), words_compact) &&
          NoDup(map(lit_var_c, words_compact)) &&
          analyze_clause_cert(anz_n, anz_F, Mstats, words_compact) &&
          analysis_tags_exact(anz_n, ms_tags(Mstats), ms_tagged(Mstats)) &&
          solver_rep_analyze_at(
            s, Mstats, reasons, levels, trail, tags, anz_wl) *
          Veci::rep_ptr(learnt, lits, words_compact)
     */
    /*@ Given Mstats words_compact */

    // clear tags
    /*@ analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mstats, anz_focus) &&
        solver_rep_analyze_at(
          s, Mstats, reasons, levels, trail, tags, anz_wl)
        which implies exists tagged_ptr,
          0 <= Zlength(ms_tagged(Mstats)) &&
          store(&(s->tags), tags) *
          CharArray::seg(tags, 0, anz_n, ms_tags(Mstats)) *
          solver_char_tail(tags, anz_n, ms_cap(Mstats)) *
          Veci::rep_ptr(&(s->tagged), tagged_ptr, ms_tagged(Mstats)) *
          solver_tags_tagged_frame_at(
            s, Mstats, reasons, levels, trail, anz_wl)
     */
    /*@ Given tagged_ptr */
    tagged = veci_begin(&s->tagged);
    /*@ Inv Assert (exists (tags_now : list Z),
          s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
          analyze_clear_loop_inv(
            anz_n, i, ms_tagged(Mstats), ms_tags(Mstats), tags_now) &&
          0 <= i && i <= Zlength(ms_tagged(Mstats)) &&
          (i == Zlength(ms_tagged(Mstats)) ||
           (i < Zlength(ms_tagged(Mstats)) &&
            0 <= ms_tagged(Mstats)[i] &&
            ms_tagged(Mstats)[i] < anz_n)) &&
          analysis_core_equiv(M, Mstats) &&
          msolver_seed_shadow(Mstats) &&
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mstats, anz_focus) &&
          analyze_clause_cert(anz_n, anz_F, Mstats, words_compact) &&
          1 <= Zlength(words_compact) && Zlength(words_compact) <= anz_n &&
          Forall(lit_wf_c(anz_n), words_compact) &&
          store(&(s->tags), tags) *
          CharArray::seg(tags, 0, anz_n, tags_now) *
          solver_char_tail(tags, anz_n, ms_cap(Mstats)) *
          Veci::rep_ptr(&(s->tagged), tagged, ms_tagged(Mstats)) *
          solver_tags_tagged_frame_at(
            s, Mstats, reasons, levels, trail, anz_wl) *
          Veci::rep_ptr(learnt, lits, words_compact) *
          has_permission(&c) * has_permission(&cnt) *
          has_permission(&p) * has_permission(&ind) *
          has_permission(&j) * has_permission(&minl)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
     */
    for (i = 0; i < veci_size(&s->tagged); i++)
        /*@ Given tags_now */
        /*@ 0 <= ms_tagged(Mstats)[i - 0] &&
              ms_tagged(Mstats)[i - 0] < anz_n &&
              CharArray::seg(tags, 0, anz_n, tags_now)
            which implies exists old_tag,
              store(pointer_offset(
                      tags, ms_tagged(Mstats)[i - 0], char), char, old_tag) *
              CharArray::missing_i(
                tags, ms_tagged(Mstats)[i - 0], 0, anz_n, tags_now)
         */
        tags[tagged[i]] = l_Undef;
    /*@ Given tags_now */
    veci_resize(&s->tagged,0);

    /*@ exists (tags_final tagged_list : list Z),
          tags_final == tags_now &&
          tagged_list == sublist(0, 0, ms_tagged(Mstats)) &&
          Zlength(tagged_list) == 0 &&
          analysis_tags_exact(anz_n, tags_final, tagged_list) &&
          store(&(s->tags), tags) *
          CharArray::seg(tags, 0, anz_n, tags_final) *
          solver_char_tail(tags, anz_n, ms_cap(Mstats)) *
          Veci::rep(&(s->tagged), tagged_list) *
          solver_tags_tagged_frame_at(
            s, Mstats, reasons, levels, trail, anz_wl)
     */
    /*@ Given tags_final tagged_list */
    /*@ analysis_core_equiv(M, Mstats) &&
          msolver_seed_shadow(Mstats) &&
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mstats, anz_focus) &&
          analyze_clause_cert(anz_n, anz_F, Mstats, words_compact) &&
          Zlength(tagged_list) == 0 &&
          analysis_tags_exact(anz_n, tags_final, tagged_list) &&
          store(&(s->tags), tags) *
          CharArray::seg(tags, 0, anz_n, tags_final) *
          solver_char_tail(tags, anz_n, ms_cap(Mstats)) *
          Veci::rep(&(s->tagged), tagged_list) *
          solver_tags_tagged_frame_at(
            s, Mstats, reasons, levels, trail, anz_wl)
        which implies exists (Mclear : msolver),
          analysis_core_equiv(M, Mclear) &&
          msolver_seed_shadow(Mclear) &&
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mclear, anz_focus) &&
          ms_tags(Mclear) == repeat_Z(0, anz_n) &&
          ms_tagged(Mclear) == nil &&
          analyze_clause_cert(anz_n, anz_F, Mclear, words_compact) &&
          solver_rep_analyze_at(
            s, Mclear, reasons, levels, trail, tags, anz_wl)
     */
    /*@ Given Mclear */

#ifdef DEBUG
    for (i = 0; i < s->size; i++)
        assert(tags[i] == l_Undef);
#endif

#ifdef VERBOSEDEBUG
    printf(L_IND"Learnt {", L_ind);
    for (i = 0; i < veci_size(learnt); i++) printf(" "L_LIT, L_lit(lits[i]));
#endif
    if (veci_size(learnt) > 1){
        /*@ analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mclear, anz_focus) &&
            solver_rep_analyze_at(
              s, Mclear, reasons, levels, trail, tags, anz_wl)
            which implies
              solver_shape(Mclear) &&
              store(&(s->reasons), reasons) *
              PtrArray::seg(reasons, 0, anz_n, ms_reason_words(Mclear)) *
              solver_ptr_tail(reasons, anz_n, ms_cap(Mclear)) *
              store(&(s->levels), levels) *
              IntArray::seg(levels, 0, anz_n, mt_levels(ms_core(Mclear))) *
              solver_int_tail(levels, anz_n, ms_cap(Mclear)) *
              solver_reason_levels_frame_at(s, Mclear, trail, tags, anz_wl)
         */
        int max_i = 1;
        /*@ Forall(lit_wf_c(anz_n), words_compact) &&
              1 < Zlength(words_compact)
            which implies
              Forall(lit_wf_c(anz_n), words_compact) &&
              1 < Zlength(words_compact) &&
              0 <= lit_var_c(words_compact[1 - 0]) &&
              lit_var_c(words_compact[1 - 0]) < anz_n
         */
        int max   = levels[lit_var(lits[1]) /*@ where(original) */];
        lit tmp;

        /*@ Inv Assert (s == s@pre && learnt == learnt@pre && levels == levels_ptr &&
              analyze_max_loop_inv(anz_n, Mclear, words_compact,
                                   i, max_i, max) &&
              2 <= i && i <= Zlength(words_compact) &&
              1 <= max_i && max_i < i &&
              Forall(lit_wf_c(anz_n), words_compact) &&
              analysis_core_equiv(M, Mclear) &&
              msolver_seed_shadow(Mclear) &&
              analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mclear, anz_focus) &&
              ms_tags(Mclear) == repeat_Z(0, anz_n) &&
              ms_tagged(Mclear) == nil &&
              analyze_clause_cert(anz_n, anz_F, Mclear, words_compact) &&
              store(&(s->reasons), reasons) *
              PtrArray::seg(reasons, 0, anz_n, ms_reason_words(Mclear)) *
              solver_ptr_tail(reasons, anz_n, ms_cap(Mclear)) *
              store(&(s->levels), levels) *
              IntArray::seg(levels, 0, anz_n, mt_levels(ms_core(Mclear))) *
              solver_int_tail(levels, anz_n, ms_cap(Mclear)) *
              solver_reason_levels_frame_at(s, Mclear, trail, tags, anz_wl) *
              Veci::rep_ptr(learnt, lits, words_compact) *
              has_permission(&c) * has_permission(&cnt) *
              has_permission(&p) * has_permission(&ind) *
              has_permission(&j) * has_permission(&minl) *
              has_permission(&tagged) * has_permission(&tmp)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
         */
        for (i = 2; i < veci_size(learnt); i++)
            /*@ Forall(lit_wf_c(anz_n), words_compact) &&
                  0 <= i && i < Zlength(words_compact)
                which implies
                  Forall(lit_wf_c(anz_n), words_compact) &&
                  0 <= i && i < Zlength(words_compact) &&
                  0 <= lit_var_c(words_compact[i - 0]) &&
                  lit_var_c(words_compact[i - 0]) < anz_n
             */
            if (levels[lit_var(lits[i]) /*@ where(original) */] > max){
                max   = levels[lit_var(lits[i]) /*@ where(original) */];
                max_i = i;
            }

        tmp         = lits[1];
        lits[1]     = lits[max_i];
        lits[max_i] = tmp;
        /*@ exists (words_sw : list Z),
              words_sw == replace_Znth(
                max_i, Znth(1, words_compact, 0),
                replace_Znth(
                  1, Znth(max_i, words_compact, 0), words_compact)) &&
              Veci::rep_ptr(learnt, lits, words_sw)
         */
        /*@ Given words_sw */

        /*@ solver_shape(Mclear) &&
              store(&(s->reasons), reasons) *
              PtrArray::seg(reasons, 0, anz_n, ms_reason_words(Mclear)) *
              solver_ptr_tail(reasons, anz_n, ms_cap(Mclear)) *
              store(&(s->levels), levels) *
              IntArray::seg(levels, 0, anz_n, mt_levels(ms_core(Mclear))) *
              solver_int_tail(levels, anz_n, ms_cap(Mclear)) *
              solver_reason_levels_frame_at(s, Mclear, trail, tags, anz_wl)
            which implies
              solver_rep_analyze_at(
                s, Mclear, reasons, levels, trail, tags, anz_wl)
         */
    }
#ifdef VERBOSEDEBUG
    {
        int lev = veci_size(learnt) > 1 ? levels[lit_var(lits[1]) /*@ where(original) */] : 0;
        printf(" } at level %d\n", lev);
    }
#endif
    /*@ exists (Mfinal : msolver) (words_final : list Z)
                      blevel,
          analysis_core_equiv(M, Mfinal) &&
          msolver_seed_shadow(Mfinal) &&
          analysis_cancel_ready(anz_n, anz_F, anz_A_arr, K, Mfinal, anz_focus) &&
          1 <= Zlength(words_final) && Zlength(words_final) <= anz_n &&
          Forall(lit_wf_c(anz_n), words_final) &&
          NoDup(map(lit_var_c, words_final)) &&
          analyze_clause_cert(anz_n, anz_F, Mfinal, words_final) &&
          analyze_backjump_cert(anz_n, Mfinal, words_final, blevel) &&
          ms_tags(Mfinal) == repeat_Z(0, anz_n) &&
          ms_tagged(Mfinal) == nil &&
          solver_rep_analyze_at(
            s, Mfinal, reasons, levels, trail, tags, anz_wl) *
          Veci::rep(learnt, words_final)
     */
    /*@ Given Mfinal */
    /*@ solver_rep_analyze_at(
          s, Mfinal, reasons, levels, trail, tags, anz_wl)
        which implies solver_rep_levels_wl_at(s, Mfinal, anz_wl, levels) *
          has_permission(&reasons) * has_permission(&trail) *
          has_permission(&tags) */

}
