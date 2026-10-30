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


/* Watched-literal propagation. */
#include "solver_qcp_internal.h"

/* Scan watches to propagate or return the conflicting clause. */
clause *solver_propagate(solver* s)
/*@ default */
{
    /*@ solver_propagation_inv(n, F, A_arr, K, M0) &&
              msolver_seed_shadow(M0) &&
              solver_rep_assigns_levels_at(s, M0, assigns_entry, levels_entry, wlists_entry)
        which implies
        exists rsn trl,
          solver_shape(M0) &&
          solver_propagation_inv(n, F, A_arr, K, M0) &&
          msolver_seed_shadow(M0) &&
          0 <= mt_qhead(ms_core(M0)) &&
          mt_qhead(ms_core(M0)) <= ms_qtail(M0) &&
          ms_qtail(M0) <= ms_size(M0) &&
          ms_size(M0) <= ms_cap(M0) &&
          Zlength(mt_trail(ms_core(M0))) == ms_qtail(M0) &&
          solver_propagate_open_at(s, M0, wlists_entry, assigns_entry, rsn,
                                   levels_entry, trl) *
          clause_db_rep(ms_prob(M0)) *
          clause_db_rep(ms_learnt(M0)) *
          solver_binary_rep(M0)
     */
    lbool*  values = s->assigns;
    clause* confl  = (clause*)0;
    lit*    lits;



    //printf("solver_propagate\n");
    /*@ Inv Assert (exists M rsn trl cf,
          s == s@pre &&
          values == assigns_entry &&
          solver_shape(M) &&
          solver_propagation_loop_inv(n, F, A_arr, K, M0, M, cf) &&
          (mt_qhead(ms_core(M0)) >= ms_qtail(M0) => M == M0 && cf == 0) &&
          minisat_propagation_reuse_loop(n, M0, M, cf) &&
          msolver_seed_shadow(M) &&
          0 <= mt_qhead(ms_core(M)) &&
          mt_qhead(ms_core(M)) <= ms_qtail(M) &&
          ms_qtail(M) <= ms_size(M) &&
          ms_size(M) <= ms_cap(M) &&
          Zlength(mt_trail(ms_core(M))) == ms_qtail(M) &&
          solver_propagate_open_at(s, M, wlists_entry, values, rsn,
                                   levels_entry, trl) *
          clause_db_rep(ms_prob(M)) *
          clause_db_rep(ms_learnt(M)) *
          solver_binary_rep(M) *
          store(&(confl), clause *, cf) *
          has_permission(&(lits))) *
          store(&l_Undef, char, 0) * store(&true, int, 1)
     */
    while (confl == 0 && s->qtail - s->qhead > 0){
        /*@ Given M rsn trl cf */
        /*@ cf == 0 &&
              mt_qhead(ms_core(M)) < ms_qtail(M) &&
              (mt_qhead(ms_core(M0)) >= ms_qtail(M0) => M == M0 && cf == 0) &&
              solver_propagation_loop_inv(n, F, A_arr, K, M0, M, cf) &&
              minisat_propagation_reuse_loop(n, M0, M, cf)
            which implies
            mt_qhead(ms_core(M0)) < ms_qtail(M0) &&
            solver_propagation_inv(n, F, A_arr, K, M) &&
            propagation_caller_frame(M0, M)
         */
        lit  p  = s->trail[s->qhead];
        s->qhead++;
        /*@ solver_propagation_inv(n, F, A_arr, K, M) &&
              p == Znth(mt_qhead(ms_core(M)), mt_trail(ms_core(M)), 0) &&
              0 <= mt_qhead(ms_core(M)) &&
              mt_qhead(ms_core(M)) < ms_qtail(M) &&
              store(&(s->wlists), vecp *, wlists_entry)
            which implies
              solver_propagation_inv(n, F, A_arr, K, M) &&
              p == Znth(mt_qhead(ms_core(M)), mt_trail(ms_core(M)), 0) &&
              0 <= p && p < 2 * n && n == ms_size(M) &&
              solver_wlists_handle(s, wlists_entry)
         */
        vecp* ws = solver_read_wlist(s,p) /*@ where rdw_wl = wlists_entry */;

        clause **begin = (clause**)vecp_begin(ws);
        clause **endvar   = begin + vecp_size(ws);
        clause **i, **j;

        s->stats.propagations++;
        s->simpdb_props = minisat_simpdb_props_after_propagation(s->simpdb_props);

        //printf("checking lit %d: "L_LIT"\n", veci_size(ws), L_lit(p));
        /*@ solver_shape(M)
            which implies
            exists Mentry source_words,
              Mentry == M &&
              source_words == Znth(Znth(mt_qhead(ms_core(M)), mt_trail(ms_core(M)), 0), ms_wm(M), nil) &&
              solver_shape(M)
         */
        j = begin;
        /*@ Inv Assert (exists Mscan watch_memory logical_words,
              exists scan_wm,
              exists retained moved rest garbage,
              exists ii jj prop_count simp_count,
              exists rsn_scan trl_scan Mentry source_words,
              s == s@pre &&
              mt_qhead(ms_core(M0)) < ms_qtail(M0) &&
          values == assigns_entry &&
              solver_shape(Mscan) &&
              msolver_seed_shadow(Mscan) &&
              propagation_caller_frame(M0, Mscan) &&
              propagation_scan_frontier(Mentry, Mscan, p) &&
              solver_propagation_scan_semantics(
                n, F, A_arr, K, Mscan, p, confl, retained, rest) &&
              minisat_propagation_reuse_scan(M0, Mscan, p, confl, rest) &&
              propagation_watch_scan_physical(
                source_words, retained, moved, rest, garbage,
                watch_memory, ii, jj) &&
              logical_words == app(retained, rest) &&
              ms_wm(Mscan) ==
                replace_Znth(p, logical_words, scan_wm) &&
              0 <= p && p < 2 * n &&
              ws == Vecp::slot(wlists_entry, p) &&
              endvar == begin + Zlength(source_words) &&
              Zlength(watch_memory) == Zlength(source_words) &&
              i == begin + ii && j == begin + jj &&
              0 <= jj && jj <= ii &&
              0 <= ii && ii <= Zlength(source_words) &&
              (ii != 0 ||
               Mscan == msolver_propagation_scan_begin(
                      Mentry, simp_count, prop_count)) &&
              simp_count == ms_simpdb_props(Mscan) &&
              prop_count == stats_propagations(ms_stats(Mscan)) &&
              0 <= Zlength(source_words) &&
              Zlength(source_words) <= INT_MAX &&
              Vecp::rep_ptr(ws, begin, watch_memory) *
              solver_wlists_handle(s, wlists_entry) *
              VecpArray::missing_i(wlists_entry, p, 0, 2 * n, scan_wm) *
              clause_db_rep(ms_prob(Mscan)) *
              clause_db_rep(ms_learnt(Mscan)) *
              CharArray::seg(
                values, 0, ms_size(Mscan),
                mt_assigns(ms_core(Mscan))) *
              solver_char_tail(
                values, ms_size(Mscan), ms_cap(Mscan)) *
              store(&(s->reasons), clause **, rsn_scan) *
              store(&(s->levels), int *, levels_entry) *
              store(&(s->trail), lit *, trl_scan) *
              PtrArray::seg(
                rsn_scan, 0, ms_size(Mscan),
                ms_reason_words(Mscan)) *
              solver_ptr_tail(
                rsn_scan, ms_size(Mscan), ms_cap(Mscan)) *
              IntArray::seg(
                levels_entry, 0, ms_size(Mscan),
                mt_levels(ms_core(Mscan))) *
              solver_int_tail(
                levels_entry, ms_size(Mscan), ms_cap(Mscan)) *
              IntArray::seg(
                trl_scan, 0, ms_qtail(Mscan),
                mt_trail(ms_core(Mscan))) *
              solver_int_tail(
                trl_scan, ms_qtail(Mscan), ms_cap(Mscan)) *
              Veci::rep(
                &(s->trail_lim), mt_lim(ms_core(Mscan))) *
              store(&(s->qhead), int,
                    mt_qhead(ms_core(Mscan))) *
              store(&(s->qtail), int, ms_qtail(Mscan)) *
              store(&(s->simpdb_props), int, simp_count) *
              store(&(s->assigns), lbool *, values) *
              store(&(s->binary), clause *, ms_binary(Mscan)) *
              solver_binary_rep(Mscan) *
              store(&(s->stats.propagations),
                    unsigned long long, prop_count) *
              store(&(s->stats.inspects), unsigned long long,
                    stats_inspects(ms_stats(Mscan))) *
              solver_propagate_frame(s, Mscan) *
              has_permission(&(lits))) *
          store(&l_Undef, char, 0) * store(&true, int, 1)
         */
        for (i = begin; i < endvar;) {
            /*@ Given Mscan watch_memory logical_words scan_wm
                      retained moved rest garbage ii jj prop_count
                      simp_count rsn_scan trl_scan Mentry source_words */
            /*@ endvar == begin + Zlength(source_words) &&
                  i == begin + ii && j == begin + jj &&
                  0 <= jj && jj <= ii &&
                  0 <= ii && ii < Zlength(source_words) &&
                  i < endvar &&
                  PtrArray::full(
                    begin, Zlength(source_words), watch_memory)
                which implies
                exists raw_prefix scan_current raw_suffix,
              endvar == begin + Zlength(source_words) &&
                  i == begin + ii && j == begin + jj &&
                  0 <= jj && jj <= ii && 0 <= ii &&
                  ii < Zlength(source_words) &&
                  0 <= scan_current &&
                  watch_memory ==
                    app(raw_prefix, cons(scan_current, raw_suffix)) &&
                  Zlength(raw_prefix) == ii &&
                  ((jj == ii &&
                    i == begin + ii &&
                    j == begin + jj &&
                    j == i &&
                    propagation_ptr_segment(
                      begin, 0, ii, raw_prefix) *
                    data_at(
                      begin + ii * sizeof(struct clause_t *),
                      struct clause_t *, scan_current) *
                    propagation_ptr_segment(
                      begin, ii + 1,
                      Zlength(source_words), raw_suffix)) ||
                   (jj < ii &&
                    i == begin + ii &&
                    j == begin + jj &&
                    propagation_ptr_segment(
                      begin, 0, jj,
                      sublist(0, jj, raw_prefix)) *
                    data_at(
                      begin + jj * sizeof(struct clause_t *),
                      struct clause_t *, Znth(jj, raw_prefix, 0)) *
                    propagation_ptr_segment(
                      begin, jj + 1, ii,
                      sublist(jj + 1, ii, raw_prefix)) *
                    data_at(
                      begin + ii * sizeof(struct clause_t *),
                      struct clause_t *, scan_current) *
                    propagation_ptr_segment(
                      begin, ii + 1,
                      Zlength(source_words), raw_suffix)))
                  $ scan_move scan_same
             */
            /*@ Given raw_prefix scan_current raw_suffix */
            if (clause_is_lit(*i)){
                *j = *i;
                /*@ app(raw_prefix,
                      cons(scan_current, raw_suffix)) == watch_memory &&
                    Zlength(raw_prefix) == ii &&
                    ii <= jj && jj <= ii &&
                    propagation_ptr_segment(
                      begin, 0, ii, raw_prefix) *
                    data_at(
                      begin + ii * sizeof(struct clause_t *),
                      struct clause_t *, scan_current) *
                    propagation_ptr_segment(
                      begin, ii + 1,
                      Zlength(source_words), raw_suffix)
                    $ scan_same
                    which implies
                    PtrArray::full(
                      begin, Zlength(source_words),
                      replace_Znth(
                        jj, scan_current, watch_memory))
                    $ scan_same
                 */
                /*@ app(raw_prefix,
                      cons(scan_current, raw_suffix)) == watch_memory &&
                    Zlength(raw_prefix) == ii &&
                    0 <= jj && jj < ii &&
                    propagation_ptr_segment(
                      begin, 0, jj,
                      sublist(0, jj, raw_prefix)) *
                    data_at(
                      begin + jj * sizeof(struct clause_t *),
                      struct clause_t *, scan_current) *
                    propagation_ptr_segment(
                      begin, jj + 1, ii,
                      sublist(jj + 1, ii, raw_prefix)) *
                    data_at(
                      begin + ii * sizeof(struct clause_t *),
                      struct clause_t *, scan_current) *
                    propagation_ptr_segment(
                      begin, ii + 1,
                      Zlength(source_words), raw_suffix)
                    $ scan_move
                    which implies
                    PtrArray::full(
                      begin, Zlength(source_words),
                      replace_Znth(
                        jj, scan_current, watch_memory))
                    $ scan_move
                 */
                /*@ PtrArray::full(
                      begin, Zlength(source_words),
                      replace_Znth(
                        jj, scan_current, watch_memory))
                    which implies
                    exists tagged_memory,
                      tagged_memory ==
                        replace_Znth(
                          jj, scan_current, watch_memory) &&
                      PtrArray::full(
                        begin, Zlength(source_words),
                        tagged_memory)
                 */
                /*@ Given tagged_memory */
                j++;
                /*@ i == begin + ii &&
                      0 <= ii &&
                      ii < Zlength(source_words) &&
                      Znth(ii, tagged_memory, 0) == scan_current &&
                      PtrArray::full(
                        begin, Zlength(source_words),
                        tagged_memory)
                    which implies
                    Znth(ii, tagged_memory, 0) ==
                      scan_current &&
                    data_at(i, Znth(ii, tagged_memory, 0)) *
                    PtrArray::missing_i(
                      begin, ii, 0, Zlength(source_words),
                      tagged_memory)
                 */
                /*@ exists rsn trl,
                    enqueue_input(ms_size(Mscan), tag_lit(scan_current),
                                  ms_qtail(Mscan), mt_assigns(ms_core(Mscan)),
                                  mt_levels(ms_core(Mscan)), ms_reason_words(Mscan),
                                  mt_trail(ms_core(Mscan))) &&
                    0 <= ms_size(Mscan) &&
                    ms_size(Mscan) <= ms_cap(Mscan) &&
                    ms_cap(Mscan) <= INT_MAX &&
                    ms_qtail(Mscan) <= ms_cap(Mscan) &&
                    data_at(i, Znth(ii, tagged_memory, 0)) *
                    store(&(s->qtail), int, ms_qtail(Mscan)) *
                    store(&(s->assigns), lbool *, values) *
                    store(&(s->levels), int *, levels_entry) *
                    store(&(s->reasons), clause **, rsn) *
                    store(&(s->trail), lit *, trl) *
                    CharArray::seg(values, 0, ms_size(Mscan),
                                   mt_assigns(ms_core(Mscan))) *
                    solver_char_tail(values, ms_size(Mscan), ms_cap(Mscan)) *
                    IntArray::seg(levels_entry, 0, ms_size(Mscan),
                                  mt_levels(ms_core(Mscan))) *
                    solver_int_tail(levels_entry, ms_size(Mscan), ms_cap(Mscan)) *
                    PtrArray::seg(rsn, 0, ms_size(Mscan),
                                  ms_reason_words(Mscan)) *
                    solver_ptr_tail(rsn, ms_size(Mscan), ms_cap(Mscan)) *
                    IntArray::seg(trl, 0, ms_qtail(Mscan),
                                  mt_trail(ms_core(Mscan))) *
                    solver_int_tail(trl, ms_qtail(Mscan), ms_cap(Mscan)) *
                    Veci::rep(&(s->trail_lim), mt_lim(ms_core(Mscan)))
                    which implies
                    enqueue_input(ms_size(Mscan), tag_lit(scan_current),
                                  ms_qtail(Mscan), mt_assigns(ms_core(Mscan)),
                                  mt_levels(ms_core(Mscan)), ms_reason_words(Mscan),
                                  mt_trail(ms_core(Mscan))) &&
                    data_at(i, Znth(ii, tagged_memory, 0)) *
                    enqueue_state_at(s, values, levels_entry,
                                  ms_size(Mscan), ms_cap(Mscan), ms_qtail(Mscan),
                                  mt_assigns(ms_core(Mscan)),
                                  mt_levels(ms_core(Mscan)), ms_reason_words(Mscan),
                                  mt_trail(ms_core(Mscan)), mt_lim(ms_core(Mscan)))
                 */
                if (!enqueue(s,clause_read_lit(*i),clause_from_lit(p))){
                    /*@ begin + ii <= i && i <= begin + ii &&
                          data_at(
                          i, Znth(ii, tagged_memory, 0)) *
                          PtrArray::missing_i(
                            begin, ii, 0, Zlength(source_words),
                            tagged_memory)
                        which implies
                        exists tagged_enqueue_conflict_memory,
                          tagged_enqueue_conflict_memory ==
                            replace_Znth(
                              ii,
                              Znth(ii, tagged_memory, 0),
                              tagged_memory) &&
                          begin + ii <= i && i <= begin + ii &&
                          PtrArray::full(
                            begin, Zlength(source_words),
                            tagged_enqueue_conflict_memory)
                     */
                    /*@ Given tagged_enqueue_conflict_memory */
                    confl = s->binary;
                    /*@ exists confl0,
                          confl == confl0 && confl0 == ms_binary(Mscan) &&
                          solver_binary_rep(Mscan) && solver_shape(Mscan)
                        which implies
                        exists confl0,
                          confl == confl0 && confl0 == ms_binary(Mscan) &&
                          solver_shape(Mscan) &&
                          store(&(confl->size_learnt), int, 4) *
                          undef_data_at(clause_lits_addr(confl), int) *
                          undef_data_at(clause_lits_addr(confl) + sizeof(int), int)
                     */
                    (clause_begin(confl))[1] =
                      lit_neg(p) /*@ where (original) */;
                    /*@ Assert (exists scratch_base0,
                          s == s@pre &&
                          mt_qhead(ms_core(M0)) < ms_qtail(M0) &&
                          values == assigns_entry &&
                          solver_shape(Mscan) &&
                          msolver_seed_shadow(Mscan) &&
                          propagation_caller_frame(M0, Mscan) &&
                          propagation_scan_frontier(Mentry, Mscan, p) &&
                          solver_propagation_scan_semantics(
                            n, F, A_arr, K, Mscan, p, 0,
                            retained, rest) &&
                          minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                          propagation_watch_scan_physical(
                            source_words, retained, moved, rest, garbage,
                            watch_memory, ii, jj) &&
                          rest == cons(scan_current, raw_suffix) &&
                          confl == ms_binary(Mscan) &&
                          clause_lits_pointer(ms_binary(Mscan), scratch_base0) &&
                          endvar == begin + Zlength(source_words) &&
                          i == begin + ii && j == begin + jj + 1 &&
                          0 <= jj && jj <= ii && 0 <= ii &&
                          ii < Zlength(source_words) && 0 <= scan_current &&
                          propagation_binary_conflict_scan_ready(
                            n, Mscan, p, scan_current, source_words, simp_count, prop_count) &&
                          watch_memory ==
                            app(raw_prefix, cons(scan_current, raw_suffix)) &&
                          Zlength(raw_prefix) == ii &&
                          tagged_enqueue_conflict_memory ==
                            replace_Znth(
                              jj, scan_current, watch_memory) &&
                          Znth(ii, tagged_enqueue_conflict_memory, 0) ==
                            scan_current &&
                          Zlength(tagged_enqueue_conflict_memory) == Zlength(source_words) &&
                          logical_words == app(retained, rest) &&
                          ms_wm(Mscan) ==
                            replace_Znth(p, logical_words, scan_wm) &&
                          0 <= p && p < 2 * n &&
                          ws == Vecp::slot(wlists_entry, p) &&
                          undef_data_at(scratch_base0, int) *
                          store(scratch_base0 + sizeof(int), int, lit_neg_c(p)) *
                          store(&(confl->size_learnt), int, 4) *
                          enqueue_post_at(s, values, levels_entry,
                                       tag_lit(scan_current), tag_of_lit(p),
                                       ms_size(Mscan), ms_cap(Mscan), ms_qtail(Mscan), 0,
                                       mt_assigns(ms_core(Mscan)),
                                       mt_levels(ms_core(Mscan)),
                                       ms_reason_words(Mscan),
                                       mt_trail(ms_core(Mscan)),
                                       mt_lim(ms_core(Mscan))) *
                          Vecp::rep_ptr(ws, begin, tagged_enqueue_conflict_memory) *
                          solver_wlists_handle(s, wlists_entry) *
                          VecpArray::missing_i(wlists_entry, p, 0, 2 * n, scan_wm) *
                          undef_data_at(&(lits), lit *) *
                          store(&(s->qhead), int,
                                mt_qhead(ms_core(Mscan))) *
                          store(&(s->simpdb_props), int, simp_count) *
                          store(&(s->binary), clause *, ms_binary(Mscan)) *
                          clause_db_rep(ms_prob(Mscan)) *
                          clause_db_rep(ms_learnt(Mscan)) *
                          store(&(s->stats.propagations), unsigned long long,
                                prop_count) *
                          store(&(s->stats.inspects), unsigned long long,
                                stats_inspects(ms_stats(Mscan))) *
                          solver_propagate_frame(s, Mscan)) *
          store(&l_Undef, char, 0) * store(&true, int, 1)
                     */
                    /*@ Given scratch_base0 */
                    /*@ i == begin + ii &&
                      0 <= ii &&
                      ii < Zlength(source_words) &&
                      Znth(ii, tagged_enqueue_conflict_memory, 0) ==
                        scan_current &&
                      PtrArray::full(
                        begin, Zlength(source_words),
                        tagged_enqueue_conflict_memory)
                        which implies
                        Znth(
                          ii,
                          tagged_enqueue_conflict_memory, 0) ==
                          scan_current &&
                        data_at(
                          i,
                          Znth(
                            ii,
                            tagged_enqueue_conflict_memory, 0)) *
                        PtrArray::missing_i(
                          begin, ii, 0, Zlength(source_words),
                          tagged_enqueue_conflict_memory)
                     */
                    /*@ confl == ms_binary(Mscan) &&
                          clause_lits_pointer(ms_binary(Mscan), scratch_base0) &&
                          undef_data_at(scratch_base0, int) *
                          store(scratch_base0 + sizeof(int), int, lit_neg_c(p))
                        which implies
                          confl == ms_binary(Mscan) &&
                          scratch_base0 ==
                            clause_lits_addr(ms_binary(Mscan)) &&
                          scratch_base0 == clause_lits_addr(confl) &&
                          clause_lits_pointer(
                            ms_binary(Mscan), scratch_base0) &&
                          undef_data_at(clause_lits_addr(confl), int) *
                          store(clause_lits_addr(confl) + sizeof(int), int,
                                lit_neg_c(p))
                     */
                    (clause_begin(confl))[0] = clause_read_lit(*i);

                    i++;

                    // Copy the remaining watches:
                    /*@ Inv Assert (exists scratch_base scratch_lits,
                          exists copy_memory copy_src copy_dst,
                          s == s@pre &&
                          mt_qhead(ms_core(M0)) < ms_qtail(M0) &&
                          values == assigns_entry &&
                          solver_shape(Mscan) &&
                          msolver_seed_shadow(Mscan) &&
                          propagation_caller_frame(M0, Mscan) &&
                          propagation_scan_frontier(Mentry, Mscan, p) &&
                          solver_propagation_scan_semantics(
                            n, F, A_arr, K, Mscan, p, 0,
                            retained, rest) &&
                          minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                          propagation_watch_scan_physical(
                            source_words, retained, moved, rest, garbage,
                            watch_memory, ii, jj) &&
                          rest == cons(scan_current, raw_suffix) &&
                          confl == ms_binary(Mscan) &&
                          clause_lits_pointer(ms_binary(Mscan), scratch_base) &&
                          Zlength(scratch_lits) == 2 &&
                          Znth(0, scratch_lits, 0) == tag_lit(scan_current) &&
                          Znth(1, scratch_lits, 0) == lit_neg_c(p) &&
                          endvar == begin + Zlength(source_words) &&
                          i == begin + copy_src &&
                          j == begin + copy_dst &&
                          0 <= copy_dst && copy_dst <= copy_src &&
                          copy_src <= Zlength(source_words) &&
                          Zlength(copy_memory) == Zlength(source_words) &&
                          binary_watch_copy_progress(
                            watch_memory, raw_prefix, scan_current,
                            raw_suffix, ii, jj, copy_src, copy_dst,
                            copy_memory) &&
                          logical_words == app(retained, rest) &&
                          ms_wm(Mscan) ==
                            replace_Znth(p, logical_words, scan_wm) &&
                          0 <= p && p < 2 * n &&
                          ws == Vecp::slot(wlists_entry, p) &&
                          propagation_binary_conflict_scan_ready(
                            n, Mscan, p, scan_current, source_words, simp_count, prop_count) &&
                          IntArray::full(scratch_base, 2, scratch_lits) *
                          store(&(confl->size_learnt), int, 4) *
                          enqueue_post_at(s, values, levels_entry,
                                       tag_lit(scan_current), tag_of_lit(p),
                                       ms_size(Mscan), ms_cap(Mscan), ms_qtail(Mscan), 0,
                                       mt_assigns(ms_core(Mscan)),
                                       mt_levels(ms_core(Mscan)),
                                       ms_reason_words(Mscan),
                                       mt_trail(ms_core(Mscan)),
                                       mt_lim(ms_core(Mscan))) *
                          Vecp::rep_ptr(ws, begin, copy_memory) *
                          solver_wlists_handle(s, wlists_entry) *
                          VecpArray::missing_i(wlists_entry, p, 0, 2 * n, scan_wm) *
                          undef_data_at(&(lits), lit *) *
                          store(&(s->qhead), int,
                                mt_qhead(ms_core(Mscan))) *
                          store(&(s->simpdb_props), int, simp_count) *
                          store(&(s->binary), clause *, ms_binary(Mscan)) *
                          clause_db_rep(ms_prob(Mscan)) *
                          clause_db_rep(ms_learnt(Mscan)) *
                          store(&(s->stats.propagations), unsigned long long,
                                prop_count) *
                          store(&(s->stats.inspects), unsigned long long,
                                stats_inspects(ms_stats(Mscan))) *
                          solver_propagate_frame(s, Mscan)) *
          store(&l_Undef, char, 0) * store(&true, int, 1)
                     */
                    while (i < endvar) {
                        /*@ Given scratch_base scratch_lits copy_memory copy_src copy_dst */
                        /*@ i == begin + copy_src &&
                              j == begin + copy_dst &&
                              0 <= copy_dst && copy_dst <= copy_src &&
                              copy_src < Zlength(source_words) &&
                              PtrArray::full(begin, Zlength(source_words),
                                             copy_memory)
                            which implies
                            ((copy_dst == copy_src &&
                              i == begin + copy_src &&
                              j == begin + copy_dst &&
                              data_at(
                                i, Znth(copy_src, copy_memory, 0)) *
                              PtrArray::missing_i(begin, copy_src, 0,
                                                  Zlength(source_words),
                                                  copy_memory)) ||
                             (copy_dst < copy_src &&
                              i == begin + copy_src &&
                              j == begin + copy_dst &&
                              PtrArray::seg(begin, 0, copy_dst,
                                            sublist(0, copy_dst,
                                                    copy_memory)) *
                              data_at(
                                j, Znth(copy_dst, copy_memory, 0)) *
                              PtrArray::seg(
                                begin, copy_dst + 1, copy_src,
                                sublist(copy_dst + 1, copy_src,
                                                    copy_memory)) *
                              data_at(
                                i, Znth(copy_src, copy_memory, 0)) *
                              PtrArray::seg(begin, copy_src + 1,
                                            Zlength(source_words),
                                            sublist(copy_src + 1,
                                                    Zlength(source_words),
                                                    copy_memory))))
                         */
                        *j = *i;
                        j++;
                        i++;
                    }
                /*@ Given scratch_base scratch_lits copy_memory copy_src copy_dst */
                /*@ propagation_scan_open(
                      n, F, A_arr, K, M0, Mentry, Mscan, p, 0,
                      source_words, retained, moved, rest, garbage,
                      watch_memory, ii, jj, scan_current, raw_suffix) &&
                    minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                    propagation_binary_conflict_scan_ready(
                      n, Mscan, p, scan_current, source_words, simp_count, prop_count) &&
                    ms_wm(Mscan) == replace_Znth(p, app(retained, rest), scan_wm) &&
                    0 <= p && p < 2 * n && ws == Vecp::slot(wlists_entry, p) &&
                    confl <= ms_binary(Mscan) &&
                    ms_binary(Mscan) <= confl &&
                    i >= endvar &&
                    endvar == begin + Zlength(source_words) &&
                    i == begin + copy_src &&
                    j == begin + copy_dst &&
                    0 <= copy_dst &&
                    copy_dst <= copy_src &&
                    copy_src <= Zlength(source_words) &&
                    Zlength(copy_memory) == Zlength(source_words) &&
                    binary_watch_copy_progress(
                      watch_memory, raw_prefix, scan_current, raw_suffix, ii,
                      jj, copy_src, copy_dst, copy_memory) &&
                    clause_lits_pointer( ms_binary(Mscan), scratch_base) &&
                    Zlength(scratch_lits) == 2 &&
                    Znth(0, scratch_lits, 0) == tag_lit(scan_current) &&
                    Znth(1, scratch_lits, 0) == lit_neg_c(p) &&
                    IntArray::full( scratch_base, 2, scratch_lits) *
                    store(&(confl->size_learnt), int, 4) *
                    enqueue_post_at(
                      s, values, levels_entry, tag_lit(scan_current),
                      tag_of_lit(p), ms_size(Mscan), ms_cap(Mscan),
                      ms_qtail(Mscan), 0, mt_assigns(ms_core(Mscan)),
                      mt_levels(ms_core(Mscan)), ms_reason_words(Mscan),
                      mt_trail(ms_core(Mscan)), mt_lim(ms_core(Mscan))) *
                    Vecp::rep_ptr(ws, begin, copy_memory) *
                    solver_wlists_handle(s, wlists_entry) *
                    VecpArray::missing_i(wlists_entry, p, 0, 2 * n, scan_wm) *
                    clause_db_rep(ms_prob(Mscan)) *
                    clause_db_rep(ms_learnt(Mscan)) *
                    store(&(s->qhead), int, mt_qhead(ms_core(Mscan))) *
                    store(&(s->simpdb_props), int, simp_count) *
                    store(&(s->binary), clause *, ms_binary(Mscan)) *
                    store(&(s->stats.propagations), unsigned long long,
                          prop_count) *
                    store(&(s->stats.inspects), unsigned long long,
                          stats_inspects(ms_stats(Mscan))) *
                    solver_propagate_frame(s, Mscan) *
                    undef_data_at(&(lits), lit *)
                    which implies
                    exists Mroute retained_route garbage_route,
                      propagation_binary_conflict_exit(
                        n, F, A_arr, K, M0, Mentry, Mscan, Mroute,
                        p, scan_current, confl,
                        source_words, retained, moved, rest, copy_memory,
                        garbage_route, retained_route) &&
                      minisat_propagation_reuse_scan(M0, Mroute, p, confl, nil) &&
                      ms_wm(Mroute) ==
                        replace_Znth(p, retained_route, scan_wm) &&
                      0 <= p && p < 2 * n &&
                      ws == Vecp::slot(wlists_entry, p) &&
                      endvar == begin + Zlength(source_words) &&
                      i == begin + Zlength(source_words) &&
                      j == begin + Zlength(retained_route) &&
                      simp_count == ms_simpdb_props(Mroute) &&
                      prop_count == stats_propagations(ms_stats(Mroute)) &&
                      0 <= Zlength(source_words) &&
                      Zlength(copy_memory) == Zlength(source_words) &&
                      Zlength(source_words) <= INT_MAX &&
                      Vecp::rep_ptr(ws, begin, copy_memory) *
                      solver_wlists_handle(s, wlists_entry) *
                      VecpArray::missing_i(wlists_entry, p, 0, 2 * n, scan_wm) *
                      clause_db_rep(ms_prob(Mroute)) *
                      clause_db_rep(ms_learnt(Mroute)) *
                      store(&(s->qhead), int, mt_qhead(ms_core(Mroute))) *
                      store(&(s->levels), int *, levels_entry) *
                      solver_propagation_scan_arrays_noqh_at(
                        s, Mroute, values, s->reasons, levels_entry, s->trail,
                        ms_simpdb_props(Mroute),
                        stats_propagations(ms_stats(Mroute))) *
                      has_permission(&(lits))
                 */
                /*@ Branch name binary_conflict */
                /*@ Assert (exists Mnext memory_next logical_next,
                          exists next_wm,
                          exists retained_next moved_next rest_next garbage_next,
                          exists ii_next jj_next prop_count_next simp_count_next,
                          exists rsn_next lvl_next trl_next,
                          exists Mentry_next source_words_next,
                          i >= endvar &&
                          mt_qhead(ms_core(M0)) < ms_qtail(M0) &&
                          lvl_next == levels_entry &&
                          s == s@pre &&
                  values == assigns_entry && solver_shape(Mnext) &&
                          msolver_seed_shadow(Mnext) &&
                          propagation_caller_frame(M0, Mnext) &&
                          propagation_scan_frontier( Mentry_next, Mnext, p) &&
                          solver_propagation_scan_semantics(
                            n, F, A_arr, K, Mnext, p, confl,
                            retained_next, rest_next) &&
                          minisat_propagation_reuse_scan(M0, Mnext, p, confl, rest_next) &&
                          propagation_watch_scan_physical(
                            source_words_next, retained_next, moved_next,
                            rest_next, garbage_next, memory_next,
                            ii_next, jj_next) &&
                          logical_next == app(retained_next, rest_next) &&
                          ms_wm(Mnext) ==
                            replace_Znth(p, logical_next, next_wm) &&
                          0 <= p && p < 2 * n &&
                          ws == Vecp::slot(wlists_entry, p) &&
                          endvar == begin + Zlength(source_words_next) &&
                          Zlength(memory_next) == Zlength(source_words_next) &&
                          i == begin + ii_next &&
                          j == begin + jj_next &&
                          0 <= jj_next && jj_next <= ii_next &&
                          0 <= ii_next &&
                          ii_next <= Zlength(source_words_next) &&
                          (ii_next != 0 ||
                           Mnext == msolver_propagation_scan_begin(
                             Mentry_next, simp_count_next, prop_count_next)) &&
                          simp_count_next == ms_simpdb_props(Mnext) &&
                          prop_count_next == stats_propagations(ms_stats(Mnext)) &&
                          0 <= Zlength(source_words_next) &&
                          Zlength(source_words_next) <= INT_MAX &&
                          Vecp::rep_ptr(ws, begin, memory_next) *
                          solver_wlists_handle(s, wlists_entry) *
                          VecpArray::missing_i(wlists_entry, p, 0, 2 * n, next_wm) *
                          clause_db_rep(ms_prob(Mnext)) *
                          clause_db_rep(ms_learnt(Mnext)) *
                          store(&(s->reasons), clause **, rsn_next) *
                          store(&(s->levels), int *, lvl_next) *
                          store(&(s->trail), lit *, trl_next) *
                          CharArray::seg(
                            values, 0, ms_size(Mnext),
                            mt_assigns(ms_core(Mnext))) *
                          solver_char_tail(
                            values, ms_size(Mnext), ms_cap(Mnext)) *
                          store(&(s->qhead), int,
                            mt_qhead(ms_core(Mnext))) *
                          solver_propagation_scan_core_at(
                            s, Mnext, values, rsn_next, lvl_next, trl_next,
                            simp_count_next, prop_count_next) *
                          has_permission(&(lits))) *
          store(&l_Undef, char, 0) * store(&true, int, 1)
                 */
                    break;
                }
            /*@ Branch name binary_keep */
            /*@ begin + ii <= i && i <= begin + ii &&
                      data_at(i, Znth(ii, tagged_memory, 0)) *
                      PtrArray::missing_i(
                        begin, ii, 0, Zlength(source_words),
                        tagged_memory)
                    $ binary_keep
                    which implies
                    exists tagged_enqueue_success_memory,
                      tagged_enqueue_success_memory ==
                        replace_Znth(
                          ii,
                          Znth(ii, tagged_memory, 0),
                          tagged_memory) &&
                      begin + ii <= i && i <= begin + ii &&
                      PtrArray::full(
                        begin, Zlength(source_words),
                        tagged_enqueue_success_memory)
                    $ binary_keep
             */
            /*@ exists enq_l enq_reason enq_ret p_v,
                  enq_ret != 0 &&
                  enq_l <= tag_lit(scan_current) &&
                  tag_lit(scan_current) <= enq_l &&
                  enq_reason <= tag_of_lit(p_v) &&
                  tag_of_lit(p_v) <= enq_reason &&
                  store(&p, int, p_v) *
                  enqueue_post_at(
                    s, values, levels_entry,
                    enq_l, enq_reason,
                    ms_size(Mscan), ms_cap(Mscan),
                    ms_qtail(Mscan), enq_ret,
                    mt_assigns(ms_core(Mscan)),
                    mt_levels(ms_core(Mscan)),
                    ms_reason_words(Mscan),
                    mt_trail(ms_core(Mscan)),
                    mt_lim(ms_core(Mscan)))
                $ binary_keep
                which implies
                  store(&p, int, p_v) *
                  enqueue_post_at(
                    s, values, levels_entry,
                    tag_lit(scan_current), tag_of_lit(p_v),
                    ms_size(Mscan), ms_cap(Mscan),
                    ms_qtail(Mscan), 1,
                    mt_assigns(ms_core(Mscan)),
                    mt_levels(ms_core(Mscan)),
                    ms_reason_words(Mscan),
                    mt_trail(ms_core(Mscan)),
                    mt_lim(ms_core(Mscan)))
                $ binary_keep
             */
            /*@ solver_propagation_scan_semantics(
                      n, F, A_arr, K, Mscan, p, 0,
                      retained, rest) &&
                minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                    tagged_word(scan_current) &&
                    rest == cons(scan_current, raw_suffix) &&
                    propagation_watch_scan_physical(source_words, retained,
                      moved, rest, garbage, watch_memory, ii, jj) &&
                    enqueue_post_at(
                      s, values, levels_entry,
                      tag_lit(scan_current), tag_of_lit(p),
                      ms_size(Mscan), ms_cap(Mscan),
                      ms_qtail(Mscan), 1,
                      mt_assigns(ms_core(Mscan)),
                      mt_levels(ms_core(Mscan)),
                      ms_reason_words(Mscan),
                      mt_trail(ms_core(Mscan)),
                      mt_lim(ms_core(Mscan)))
                    $ binary_keep
                    which implies
                    exists Mroute retained_route rest_route,
                      exists garbage_route memory_route,
                      retained_route ==
                        app(retained, cons(scan_current, nil)) &&
                      rest_route == raw_suffix &&
                      propagation_binary_keep_transition(
                        n, F, A_arr, K, Mscan, p,
                        scan_current, retained_route,
                        rest_route, Mroute) &&
                      minisat_propagation_reuse_scan(M0, Mroute, p, 0, rest_route) &&
                      propagation_scan_keep_step(
                        source_words, retained, moved, rest,
                        watch_memory, ii, jj, scan_current,
                        retained_route, rest_route,
                        garbage_route, memory_route) &&
                      enqueue_post_at(
                        s, values, levels_entry,
                        tag_lit(scan_current), tag_of_lit(p),
                        ms_size(Mscan), ms_cap(Mscan),
                        ms_qtail(Mscan), 1,
                        mt_assigns(ms_core(Mscan)),
                        mt_levels(ms_core(Mscan)),
                        ms_reason_words(Mscan),
                        mt_trail(ms_core(Mscan)),
                        mt_lim(ms_core(Mscan)))
                    $ binary_keep
             */
            }else{
                lit false_lit;
                lbool sig;

                /*@ solver_propagation_scan_semantics(
                      n, F, A_arr, K, Mscan, p, 0,
                      retained, rest) &&
                    minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                    propagation_watch_scan_physical(
                      source_words, retained, moved, rest, garbage,
                      watch_memory, ii, jj) &&
                    logical_words == app(retained, rest) &&
                    ms_wm(Mscan) ==
                      replace_Znth(p, logical_words, scan_wm) &&
                    watch_memory == app(raw_prefix, cons(scan_current, raw_suffix)) &&
                    Zlength(raw_prefix) == ii &&
                    0 <= p && p < 2 * n &&
                    clause_is_lit_result(scan_current, 0) &&
                    solver_shape(Mscan) &&
                    data_at(i, scan_current) *
                      clause_db_rep(ms_prob(Mscan)) *
                      clause_db_rep(ms_learnt(Mscan))
                    which implies
                    exists clause_contents,
                      0 <= p && p < 2 * n &&
                      3 <= Zlength(clause_contents) &&
                      Forall(lit_wf_c(n), clause_contents) &&
                      0 <= Znth(0, clause_contents, 0) &&
                      Znth(0, clause_contents, 0) < 2 * n &&
                      0 <= Znth(1, clause_contents, 0) &&
                      Znth(1, clause_contents, 0) < 2 * n &&
                      0 <= lit_var_c(Znth(0, clause_contents, 0)) &&
                      lit_var_c(Znth(0, clause_contents, 0)) < ms_size(Mscan) &&
                      0 <= lit_var_c(Znth(1, clause_contents, 0)) &&
                      lit_var_c(Znth(1, clause_contents, 0)) < ms_size(Mscan) &&
                      clause_db_pair_contents(ms_prob(Mscan), ms_learnt(Mscan),
                                              scan_current, clause_contents) &&
                      data_at(i, scan_current) *
                      clause_db_pair_focus(ms_prob(Mscan), ms_learnt(Mscan),
                                           scan_current, clause_contents)
                 */
                /*@ Given clause_contents */
                /*@ clause_db_pair_focus(ms_prob(Mscan), ms_learnt(Mscan),
                                         scan_current, clause_contents)
                    which implies
                      clause_db_pair_frame(ms_prob(Mscan), ms_learnt(Mscan),
                                           scan_current, clause_contents) *
                      IntArray::full(clause_lits_addr(scan_current),
                                     Zlength(clause_contents),
                                     clause_contents)
                 */
                lits = clause_begin(*i);

                // Make sure the false literal is data[1]:
                /*@ exists clause_base,
                      clause_lits_pointer(scan_current, clause_base) &&
                      2 <= Zlength(clause_contents) &&
                      lits == clause_base &&
                      IntArray::full(clause_base,
                                     Zlength(clause_contents),
                                     clause_contents)
                    which implies
                      clause_lits_pointer(scan_current, lits) &&
                      store(lits + 0 * sizeof(int), int,
                            Znth(0, clause_contents, 0)) *
                      store(lits + 1 * sizeof(int), int,
                            Znth(1, clause_contents, 0)) *
                      IntArray::seg(lits, 2,
                                    Zlength(clause_contents),
                                    sublist(2, Zlength(clause_contents),
                                            clause_contents))
                 */
                /*@ solver_propagation_scan_semantics(
                      n, F, A_arr, K, Mscan, p, confl,
                      retained, rest) &&
                    minisat_propagation_reuse_scan(M0, Mscan, p, confl, rest) &&
                    propagation_watch_scan_physical(
                      source_words, retained, moved, rest, garbage,
                      watch_memory, ii, jj) &&
                    logical_words == app(retained, rest) &&
                    ms_wm(Mscan) ==
                      replace_Znth(p, logical_words, scan_wm) &&
                    watch_memory == app(raw_prefix, cons(scan_current, raw_suffix)) &&
                    Zlength(raw_prefix) == ii &&
                    0 <= p && p < 2 * n &&
                    clause_is_lit_result(scan_current, 0) &&
                    clause_db_pair_contents(ms_prob(Mscan), ms_learnt(Mscan),
                                            scan_current, clause_contents)
                    which implies
                    real_watch_pair(p, clause_contents) &&
                    (Znth(0, clause_contents, 0) == lit_neg_c(p) ||
                     Znth(1, clause_contents, 0) == lit_neg_c(p)) &&
                    rest == cons(scan_current, raw_suffix) &&
                    confl == 0 &&
                    solver_propagation_scan_semantics(
                      n, F, A_arr, K, Mscan, p, 0, retained, rest) &&
                    minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest)
                 */
                false_lit = lit_neg(p) /*@ where (original) */;
                if (lits[0] == false_lit){
                    lits[0] = lits[1];
                    lits[1] = false_lit;
                }
                /*@ exists w0 w1,
                      w1 == lit_neg_c(p) &&
                      0 <= w0 && w0 < 2 * n &&
                      w0 + w1 ==
                        Znth(0, clause_contents, 0) +
                        Znth(1, clause_contents, 0) &&
                      real_watch_pair(p, clause_contents) &&
                      store(lits + 0 * sizeof(int), int, w0) *
                      store(lits + 1 * sizeof(int), int, w1)
                    which implies
                      w1 == lit_neg_c(p) &&
                      0 <= w0 && w0 < 2 * n &&
                      0 <= lit_sign_c(w0) && lit_sign_c(w0) <= 1 &&
                      w0 + w1 ==
                        Znth(0, clause_contents, 0) +
                        Znth(1, clause_contents, 0) &&
                      real_watch_pair(p, clause_contents) &&
                      store(lits + 0 * sizeof(int), int, w0) *
                      store(lits + 1 * sizeof(int), int, w1)
                 */
                assert(lits[1] == false_lit);
                //printf("checking clause: "); printlits(lits, lits+clause_size(*i)); printf("\n");

                // If 0th watch is true, then clause is already satisfied.
                sig = !lit_sign(lits[0]); sig += sig - 1;
                if (values[lit_var(lits[0]) /*@ where(original) */] == sig){
                    *j = *i;
                    /*@ app(raw_prefix,
                          cons(scan_current, raw_suffix)) == watch_memory &&
                        Zlength(raw_prefix) == ii &&
                        ii <= jj && jj <= ii &&
                        propagation_ptr_segment(
                          begin, 0, ii, raw_prefix) *
                        data_at(
                          begin + ii * sizeof(struct clause_t *),
                          struct clause_t *, scan_current) *
                        propagation_ptr_segment(
                          begin, ii + 1,
                          Zlength(source_words), raw_suffix)
                        $ scan_same
                        which implies
                        PtrArray::full(
                          begin, Zlength(source_words),
                          replace_Znth(
                            jj, scan_current, watch_memory))
                        $ scan_same
                     */
                    /*@ app(raw_prefix,
                          cons(scan_current, raw_suffix)) == watch_memory &&
                        Zlength(raw_prefix) == ii &&
                        0 <= jj && jj < ii &&
                        propagation_ptr_segment(
                          begin, 0, jj,
                          sublist(0, jj, raw_prefix)) *
                        data_at(
                          begin + jj * sizeof(struct clause_t *),
                          struct clause_t *, scan_current) *
                        propagation_ptr_segment(
                          begin, jj + 1, ii,
                          sublist(jj + 1, ii, raw_prefix)) *
                        data_at(
                          begin + ii * sizeof(struct clause_t *),
                          struct clause_t *, scan_current) *
                        propagation_ptr_segment(
                          begin, ii + 1,
                          Zlength(source_words), raw_suffix)
                        $ scan_move
                        which implies
                        PtrArray::full(
                          begin, Zlength(source_words),
                          replace_Znth(
                            jj, scan_current, watch_memory))
                        $ scan_move
                     */
                    j++;
                /*@ exists watch0,
                          solver_propagation_scan_semantics(
                            n, F, A_arr, K, Mscan, p, 0,
                            retained, rest) &&
                          minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                          rest == cons(scan_current, raw_suffix) &&
                          propagation_watch_scan_physical(
                            source_words, retained, moved, rest, garbage,
                            watch_memory, ii, jj) &&
                          clause_lits_pointer(scan_current, lits) &&
                          3 <= Zlength(clause_contents) &&
                          real_watch_pair(p, clause_contents) &&
                          0 <= p && p < 2 * n &&
                          false_lit == lit_neg_c(p) &&
                          watch0 + false_lit ==
                            Znth(0, clause_contents, 0) +
                            Znth(1, clause_contents, 0) &&
                          sig == 1 - 2 * lit_sign_c(watch0) &&
                          Znth(lit_var_c(watch0),
                               mt_assigns(ms_core(Mscan)), 0) == sig &&
                          clause_db_pair_frame(
                            ms_prob(Mscan), ms_learnt(Mscan),
                            scan_current, clause_contents) *
                          store(lits + 0 * sizeof(int), int, watch0) *
                          store(lits + 1 * sizeof(int), int, false_lit) *
                          IntArray::seg(
                            lits, 2, Zlength(clause_contents),
                            sublist(2, Zlength(clause_contents),
                                    clause_contents))
                        which implies
                        exists watch0 prob_route learnt_route Mroute,
                          exists retained_route rest_route,
                          exists garbage_route memory_route,
                          db_pair_lits_update(
                            ms_prob(Mscan), ms_learnt(Mscan),
                            scan_current, clause_contents,
                            propagation_normalized_clause(
                              watch0, false_lit, clause_contents),
                            prob_route, learnt_route) &&
                          retained_route ==
                            app(retained, cons(scan_current, nil)) &&
                          rest_route == raw_suffix &&
                          propagation_real_satisfied_transition(
                            n, F, A_arr, K, Mscan, p,
                            prob_route, learnt_route,
                            retained_route, rest_route, Mroute) &&
                          minisat_propagation_reuse_scan(M0, Mroute, p, 0, rest_route) &&
                          propagation_scan_keep_step(
                            source_words, retained, moved, rest,
                            watch_memory, ii, jj, scan_current,
                            retained_route, rest_route,
                            garbage_route, memory_route) &&
                          clause_db_rep(prob_route) *
                          clause_db_rep(learnt_route) *
                          has_permission(&lits) *
                          has_permission(&sig)
                 */
                /*@ Given watch0 prob_route learnt_route Mroute retained_route rest_route */
                /*@ Branch name real_satisfied */
                }else{
                    // Look for new watch:
                    /*@ clause_db_pair_frame(
                          ms_prob(Mscan), ms_learnt(Mscan),
                          scan_current, clause_contents)
                        which implies exists (is_learnt_scan : bool),
                          clause_hdr_word(
                            is_learnt_scan,
                            Zlength(clause_contents)) / 2 ==
                              Zlength(clause_contents) &&
                          store(clause_hdr_addr(scan_current), int,
                                clause_hdr_word(
                                  is_learnt_scan,
                                  Zlength(clause_contents))) *
                          activity_state(scan_current, is_learnt_scan, Zlength(clause_contents)) *
                          clause_db_pair_remainder(
                            ms_prob(Mscan), ms_learnt(Mscan),
                            scan_current, is_learnt_scan, clause_contents)
                     */
                    /*@ Given is_learnt_scan */
                    lit* stop = lits + clause_size(*i);
                    /*@ store(clause_hdr_addr(scan_current), int,
                              clause_hdr_word(
                                is_learnt_scan,
                                Zlength(clause_contents))) *
                        activity_state(scan_current, is_learnt_scan, Zlength(clause_contents)) *
                        clause_db_pair_remainder(
                          ms_prob(Mscan), ms_learnt(Mscan),
                          scan_current, is_learnt_scan, clause_contents)
                        which implies
                        clause_db_pair_frame(
                          ms_prob(Mscan), ms_learnt(Mscan),
                          scan_current, clause_contents)
                     */
                    /*@ app(raw_prefix,
                          cons(scan_current, raw_suffix)) == watch_memory &&
                        Zlength(raw_prefix) == ii &&
                        propagation_ptr_segment(
                          begin, 0, ii, raw_prefix) *
                        data_at(
                          begin + ii * sizeof(struct clause_t *),
                          struct clause_t *, scan_current) *
                        propagation_ptr_segment(
                          begin, ii + 1,
                          Zlength(source_words), raw_suffix)
                        $ scan_same
                        which implies
                        PtrArray::full(
                          begin, Zlength(source_words), watch_memory)
                        $ scan_same
                     */
                    /*@ app(raw_prefix,
                          cons(scan_current, raw_suffix)) == watch_memory &&
                        Zlength(raw_prefix) == ii &&
                        0 <= jj && jj < ii &&
                        propagation_ptr_segment(
                          begin, 0, jj,
                          sublist(0, jj, raw_prefix)) *
                        data_at(
                          begin + jj * sizeof(struct clause_t *),
                          struct clause_t *, Znth(jj, raw_prefix, 0)) *
                        propagation_ptr_segment(
                          begin, jj + 1, ii,
                          sublist(jj + 1, ii, raw_prefix)) *
                        data_at(
                          begin + ii * sizeof(struct clause_t *),
                          struct clause_t *, scan_current) *
                        propagation_ptr_segment(
                          begin, ii + 1,
                          Zlength(source_words), raw_suffix)
                        $ scan_move
                        which implies
                        PtrArray::full(
                          begin, Zlength(source_words), watch_memory)
                        $ scan_move
                     */
                    /*@ PtrArray::full(
                          begin, Zlength(source_words), watch_memory)
                        which implies
                        exists candidate_post_memory,
                          candidate_post_memory == watch_memory &&
                          PtrArray::full(
                            begin, Zlength(source_words),
                            candidate_post_memory)
                     */
                    /*@ Given candidate_post_memory */
                    lit* k;
                    /*@ exists watch0_base,
                          0 <= watch0_base && watch0_base < 2 * n &&
                          solver_propagation_scan_semantics(
                            n, F, A_arr, K, Mscan, p, 0, retained, rest) &&
                          minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                          propagation_scan_frontier(Mentry, Mscan, p) &&
                          solver_shape(Mscan) &&
                          real_watch_pair(p, clause_contents) &&
                          0 <= p && p < 2 * n &&
                          Forall(lit_wf_c(n), clause_contents) &&
                          3 <= Zlength(clause_contents) &&
                          false_lit == lit_neg_c(p) &&
                          store(lits + 0 * sizeof(int), int, watch0_base) *
                          store(lits + 1 * sizeof(int), int, false_lit)
                        which implies
                          0 <= p && p < 2 * n &&
                          propagation_replacement_scan_inv(
                            n, Mscan, false_lit,
                            propagation_normalized_clause(watch0_base, false_lit,
                              clause_contents), 2) &&
                          store(lits + 0 * sizeof(int), int, watch0_base) *
                          store(lits + 1 * sizeof(int), int, false_lit)
                     */
                    /*@ Inv Assert (exists offset watch0,
                          s == s@pre &&
                          mt_qhead(ms_core(M0)) < ms_qtail(M0) &&
                          values == assigns_entry &&
                          solver_shape(Mscan) &&
                          msolver_seed_shadow(Mscan) &&
                          propagation_caller_frame(M0, Mscan) &&
                          propagation_scan_frontier(Mentry, Mscan, p) &&
                          solver_propagation_scan_semantics(
                            n, F, A_arr, K, Mscan, p, 0, retained, rest) &&
                          minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                          simp_count == ms_simpdb_props(Mscan) &&
                          prop_count == stats_propagations(ms_stats(Mscan)) &&
                          propagation_watch_scan_physical(
                            source_words, retained, moved, rest, garbage,
                            watch_memory, ii, jj) &&
                          rest == cons(scan_current, raw_suffix) &&
                          confl == 0 &&
                          endvar == begin + Zlength(source_words) &&
                          i == begin + ii &&
                          j == begin + jj &&
                          0 <= jj &&
                          jj <= ii &&
                          0 <= ii &&
                          ii < Zlength(source_words) &&
                          0 <= scan_current &&
                          watch_memory ==
                            app(raw_prefix, cons(scan_current, raw_suffix)) &&
                          Zlength(raw_prefix) == ii &&
                          candidate_post_memory == watch_memory &&
                          Znth(ii, candidate_post_memory, 0) ==
                            scan_current &&
                          logical_words == app(retained, rest) &&
                          ms_wm(Mscan) ==
                            replace_Znth(p, logical_words, scan_wm) &&
                          0 <= p && p < 2 * n &&
                          ws == Vecp::slot(wlists_entry, p) &&
                          clause_lits_pointer(scan_current, lits) &&
                          3 <= Zlength(clause_contents) &&
                          false_lit == lit_neg_c(p) &&
                          real_watch_pair(
                            p, clause_contents) &&
                          watch0 + false_lit ==
                            Znth(0, clause_contents, 0) +
                            Znth(1, clause_contents, 0) &&
                          stop == lits + Zlength(clause_contents) &&
                          k == lits + offset &&
                          2 <= offset &&
                          offset <= Zlength(clause_contents) &&
                          propagation_replacement_scan_inv(
                            n, Mscan, false_lit,
                            propagation_normalized_clause(watch0, false_lit,
                              clause_contents), offset) &&
                          -1 <= sig &&
                          sig <= 1 &&
                          0 <= Zlength(source_words) &&
                          Zlength(candidate_post_memory) == Zlength(source_words) &&
                          Zlength(source_words) <= INT_MAX &&
                          Vecp::rep_ptr(ws, begin, candidate_post_memory) *
                          solver_wlists_handle(s, wlists_entry) *
                          VecpArray::missing_i(wlists_entry, p, 0, 2 * n, scan_wm) *
                          clause_db_pair_frame(
                            ms_prob(Mscan), ms_learnt(Mscan), scan_current,
                            clause_contents) *
                          store(lits + 0 * sizeof(int), int, watch0) *
                          store(lits + 1 * sizeof(int), int, false_lit) *
                          IntArray::seg(
                            lits, 2, Zlength(clause_contents),
                            sublist(2, Zlength(clause_contents),
                                    clause_contents)) *
                          CharArray::seg(
                            values, 0, ms_size(Mscan),
                            mt_assigns(ms_core(Mscan))) *
                          solver_char_tail(
                            values, ms_size(Mscan), ms_cap(Mscan)) *
                          store(&(s->levels), int *, levels_entry) *
                          store(&(s->qhead), int, mt_qhead(ms_core(Mscan))) *
                          store(&(s->reasons), clause **, rsn_scan) *
                          store(&(s->trail), lit *, trl_scan) *
                          solver_propagation_scan_core_at(
                            s, Mscan, values, rsn_scan, levels_entry,
                            trl_scan, simp_count, prop_count)) *
          store(&l_Undef, char, 0) * store(&true, int, 1)
                     */
                    for (k = lits + 2; k < stop; k++){
                        /*@ Given watch0 offset */
                        /*@ k == lits + offset &&
                              2 <= offset &&
                              offset < Zlength(clause_contents) &&
                              IntArray::seg(
                                lits, 2, Zlength(clause_contents),
                                sublist(2, Zlength(clause_contents),
                                        clause_contents))
                            which implies
                            exists candidate,
                              k == lits + offset &&
                              2 <= offset &&
                              offset < Zlength(clause_contents) &&
                              candidate ==
                                Znth(offset - 2,
                                  sublist(2, Zlength(clause_contents),
                                          clause_contents), 0) &&
                              data_at(k, candidate) *
                              propagation_int_missing(
                                lits, offset, 2,
                                Zlength(clause_contents),
                                sublist(2, Zlength(clause_contents),
                                        clause_contents))
                         */
                        /*@ Given candidate */
                        /*@ 0 <= lit_var_c(candidate) &&
                              lit_var_c(candidate) < ms_size(Mscan)
                         */
                        lbool sig = lit_sign(*k); sig += sig - 1;
                        if (values[lit_var(*k) /*@ where(original) */] != sig){
                            /*@ 0 <= lit_var_c(candidate) &&
                                  lit_var_c(candidate) < ms_size(Mscan)
                                which implies
                                0 <= lit_neg_c(candidate) &&
                                lit_neg_c(candidate) <
                                  2 * ms_size(Mscan)
                             */
                            /*@ data_at(k, candidate) *
                                propagation_int_missing(
                                  lits, offset, 2,
                                  Zlength(clause_contents),
                                  sublist(2, Zlength(clause_contents),
                                          clause_contents))
                                which implies
                                data_at(k, candidate) *
                                IntArray::missing_i(
                                  lits, offset, 2,
                                  Zlength(clause_contents),
                                  sublist(2, Zlength(clause_contents),
                                          clause_contents))
                             */
                            /*@ solver_shape(Mscan) &&
                                  ms_wm(Mscan) ==
                                    replace_Znth(p, logical_words, scan_wm)
                                which implies
                                Zlength(scan_wm) == 2 * ms_size(Mscan) &&
                                ms_wm(Mscan) ==
                                  replace_Znth(p, logical_words, scan_wm)
                             */
                            /*@ solver_propagation_scan_semantics(
                                  n, F, A_arr, K, Mscan,
                                  p, confl,
                                  retained, rest) &&
                                minisat_propagation_reuse_scan(M0, Mscan, p, confl, rest) &&
                                  real_watch_pair(
                                    p, clause_contents) &&
                                  2 <= offset &&
                                  offset < Zlength(clause_contents) &&
                                  candidate ==
                                    Znth(offset - 2,
                                      sublist(2,
                                        Zlength(clause_contents),
                                        clause_contents), 0) &&
                                  clause_db_pair_frame(
                                    ms_prob(Mscan), ms_learnt(Mscan),
                                    scan_current, clause_contents)
                                which implies
                                solver_propagation_scan_semantics(
                                  n, F, A_arr, K, Mscan,
                                  p, confl,
                                  retained, rest) &&
                                minisat_propagation_reuse_scan(M0, Mscan, p, confl, rest) &&
                                propagation_destination_ok(
                                  2 * ms_size(Mscan), p,
                                  lit_neg_c(candidate)) &&
                                clause_db_pair_frame(
                                  ms_prob(Mscan), ms_learnt(Mscan),
                                  scan_current, clause_contents)
                             */
                            /*@ propagation_destination_ok(
                                  2 * ms_size(Mscan), p,
                                  lit_neg_c(candidate)) &&
                                  Zlength(scan_wm) == 2 * ms_size(Mscan) &&
                                  VecpArray::missing_i(wlists_entry, p, 0, 2 * n, scan_wm)
                                which implies
                                VecpArray::missing2(
                                  wlists_entry, p, lit_neg_c(candidate), 2 * n, scan_wm) *
                                Vecp::rep(
                                  Vecp::slot(wlists_entry, lit_neg_c(candidate)),
                                  Znth(lit_neg_c(candidate), scan_wm, nil))
                             */

                            lits[1] = *k;
                            *k = false_lit;
                            /*@ 2 <= offset && offset < Zlength(clause_contents) &&
                                  store(lits + 1 * sizeof(int), int,
                                    replace_Znth(offset - 2, candidate,
                                      sublist(2, Zlength(clause_contents), clause_contents))[offset - 2])
                                which implies
                                  store(lits + 1 * sizeof(int), int, candidate)
                             */
                            /*@ i == begin + ii &&
                                  0 <= ii &&
                                  ii < Zlength(source_words) &&
                                  Znth(ii, candidate_post_memory, 0) ==
                                    scan_current &&
                                  PtrArray::full(
                                    begin, Zlength(source_words),
                                    candidate_post_memory)
                                which implies
                                Znth(
                                  ii, candidate_post_memory, 0) ==
                                  scan_current &&
                                data_at(i, scan_current) *
                                PtrArray::missing_i(
                                  begin, ii, 0,
                                  Zlength(source_words),
                                  candidate_post_memory)
                             */
                            vecp_push(solver_read_wlist(s, lit_neg(lits[1]) /*@ where (original) */)
                                        /*@ where rdw_wl = wlists_entry */, *i) /*@ where
                                            l =
                                              Znth(lit_neg_c(candidate), scan_wm, nil) */
                            ;
                            /*@ exists (destination_words_now : list Z),
                                  Znth(ii, candidate_post_memory, 0) == scan_current &&
                                  0 <= ii && ii < Zlength(candidate_post_memory) &&
                                  destination_words_now == app(Znth(lit_neg_c(candidate), scan_wm, nil), cons(replace_Znth(ii, scan_current, candidate_post_memory)[ii], nil)) &&
                                  Vecp::rep(Vecp::slot(wlists_entry, lit_neg_c(candidate)),
                                    destination_words_now)
                                which implies
                                exists (destination_words_now : list Z),
                                  destination_words_now == app(Znth(lit_neg_c(candidate), scan_wm, nil), cons(scan_current, nil)) &&
                                  Vecp::rep(
                                    Vecp::slot(wlists_entry, lit_neg_c(candidate)),
                                    destination_words_now)
                             */
                            /*@ Given destination_words_now */
                            /*@ destination_words_now == app(Znth(lit_neg_c(candidate), scan_wm, nil), cons(scan_current, nil)) &&
                                  Vecp::rep(
                                    Vecp::slot(wlists_entry, lit_neg_c(candidate)),
                                    destination_words_now)
                                which implies exists destination_index,
                                  propagation_real_migrated_physical_alias(
                                    wlists_entry,
                                    lit_neg_c(candidate), scan_current,
                                    destination_index,
                                    Vecp::slot(wlists_entry, lit_neg_c(candidate)),
                                    scan_wm,
                                    destination_words_now) &&
                                  Vecp::rep(
                                    Vecp::slot(wlists_entry, lit_neg_c(candidate)),
                                    destination_words_now)
                             */

                            /*@ Znth(ii, candidate_post_memory, 0) == scan_current &&
                                  0 <= ii &&
                                  ii < Zlength(source_words) &&
                                  PtrArray::full(
                                    begin, Zlength(source_words),
                                    replace_Znth(ii, scan_current, candidate_post_memory))
                                which implies
                                exists migration_post_memory,
                                  migration_post_memory ==
                                    replace_Znth(ii, scan_current, candidate_post_memory) &&
                                  Znth(ii, migration_post_memory, 0) ==
                                    scan_current &&
                                  PtrArray::full(
                                    begin, Zlength(source_words),
                                    migration_post_memory)
                             */
                            /*@ Given migration_post_memory */
                            /*@ Branch name real_migrated */
                            /*@ exists candidate destination_index destination_ptr,
                                exists destination_words migration_post_memory,
                                  solver_shape(Mscan) && msolver_seed_shadow(Mscan) && propagation_caller_frame(M0, Mscan) &&
                                  propagation_scan_frontier(Mentry, Mscan, p) &&
                                  solver_propagation_scan_semantics(n, F, A_arr, K, Mscan, p, 0, retained, rest) &&
                                  minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                                  rest == cons(scan_current, raw_suffix) &&
                                  propagation_watch_scan_physical(source_words, retained, moved, rest,
                                    garbage, watch_memory, ii, jj) &&
                                  candidate_post_memory == watch_memory && 0 <= ii && ii < Zlength(source_words) &&
                                  Znth(ii, candidate_post_memory, 0) == scan_current && migration_post_memory ==
                                    replace_Znth(ii, Znth(ii, candidate_post_memory, 0), candidate_post_memory) &&
                                  Znth(ii, migration_post_memory, 0) == scan_current &&
                                  0 <= p && p < 2 * n && false_lit == lit_neg_c(p) &&
                                  real_watch_pair(p, clause_contents) &&
                                  watch0 + false_lit == Znth(0, clause_contents, 0) +
                                    Znth(1, clause_contents, 0) &&
                                  propagation_replacement_scan_inv(n, Mscan, false_lit,
                                    propagation_normalized_clause(watch0, false_lit, clause_contents), offset) &&
                                  propagation_scan_candidate_layout(scan_current, lits, stop, k, offset,
                                    false_lit, p, candidate, 2 * lit_sign_c(candidate) - 1, clause_contents) &&
                                  Znth(lit_var_c(candidate), mt_assigns(ms_core(Mscan)), 0) !=
                                    2 * lit_sign_c(candidate) - 1 &&
                                  propagation_destination_ok(2 * ms_size(Mscan), p, lit_neg_c(candidate)) &&
                                  propagation_real_migrated_physical_alias(
                                    wlists_entry, lit_neg_c(candidate), scan_current,
                                    destination_index, destination_ptr, scan_wm,
                                    destination_words) &&
                                  propagation_scan_slot(Mscan, p, scan_wm, logical_words) &&
                                  simp_count == ms_simpdb_props(Mscan) &&
                                  prop_count == stats_propagations(ms_stats(Mscan)) &&
                                  clause_lits_pointer(scan_current, lits) &&
                                  clause_db_pair_frame(ms_prob(Mscan), ms_learnt(Mscan),
                                    scan_current, clause_contents) *
                                  store(lits + 0 * sizeof(int), int, watch0) *
                                  store(lits + 1 * sizeof(int), int, candidate) *
                                  IntArray::seg(lits, 2, Zlength(clause_contents),
                                    replace_Znth(offset - 2, false_lit,
                                      replace_Znth(offset - 2, candidate,
                                        sublist(2, Zlength(clause_contents), clause_contents)))) *
                                  PtrArray::full(begin, Zlength(source_words), migration_post_memory) *
                                  solver_wlists_handle(s, wlists_entry) *
                                  VecpArray::missing2(wlists_entry, p, destination_index, 2 * n,
                                    scan_wm) *
                                  Vecp::rep(destination_ptr, destination_words)
                                $ real_migrated
                                which implies
                                  exists prob_route learnt_route Mroute,
                                    exists moved_route rest_route garbage_route,
                                    db_pair_lits_update(ms_prob(Mscan), ms_learnt(Mscan),
                                      scan_current, clause_contents,
                                      propagation_migrated_clause(watch0, candidate, false_lit,
                                        offset, clause_contents), prob_route, learnt_route) &&
                                    moved_route == app(moved, cons(scan_current, nil)) &&
                                    rest_route == raw_suffix &&
                                    propagation_real_migrated_exit_carrier(n, F, A_arr, K,
                                      M0, Mentry, Mscan, Mroute, p, prob_route, learnt_route,
                                      scan_wm, candidate, scan_current,
                                      source_words, retained, moved, rest, watch_memory, ii, jj,
                                      moved_route, rest_route, garbage_route,
                                      migration_post_memory, simp_count, prop_count) &&
                                    minisat_propagation_reuse_scan(M0, Mroute, p, 0, rest_route) &&
                                    clause_db_rep(prob_route) * clause_db_rep(learnt_route) *
                                    solver_wlists_handle(s, wlists_entry) *
                                    VecpArray::missing_i(wlists_entry, p, 0, 2 * n,
                                      replace_Znth(destination_index, destination_words, scan_wm)) *
                                    PtrArray::full(begin, Zlength(source_words), migration_post_memory) *
                                    has_permission(&k) * has_permission(&lits) *
                                    has_permission(&stop)
                                $ real_migrated
                             */
                            goto next; }
                        /*@ propagation_replacement_scan_inv(
                              n, Mscan, false_lit,
                              propagation_normalized_clause(
                                watch0, false_lit, clause_contents),
                              offset) &&
                              3 <= Zlength(clause_contents) &&
                              offset < Zlength(clause_contents) &&
                              candidate == Znth(
                                offset,
                                propagation_normalized_clause(
                                  watch0, false_lit, clause_contents), 0) &&
                              sig == 2 * lit_sign_c(candidate) - 1 &&
                              Znth(lit_var_c(candidate),
                                mt_assigns(ms_core(Mscan)), 0) == sig
                            which implies
                                propagation_replacement_scan_inv(
                                  n, Mscan, false_lit,
                                  propagation_normalized_clause(
                                  watch0, false_lit, clause_contents),
                                  offset + 1) &&
                              has_permission(&sig)
                         */
                    }

                    /*@ Given watch0 offset */
                        /*@ propagation_replacement_scan_inv(
                              n, Mscan, false_lit,
                              propagation_normalized_clause(
                                watch0, false_lit, clause_contents),
                              offset) &&
                              k == lits + offset && k == stop &&
                              stop == lits + Zlength(clause_contents) &&
                              3 <= Zlength(clause_contents)
                            which implies
                              k == lits + offset && k == stop &&
                              stop == lits + Zlength(clause_contents) &&
                              propagation_replacement_scan_inv(
                                n, Mscan, false_lit,
                                propagation_normalized_clause(
                                  watch0, false_lit, clause_contents),
                                Zlength(clause_contents))
                         */
                        /*@ i == begin + ii &&
                              j == begin + jj &&
                              0 <= jj && jj <= ii &&
                              0 <= ii &&
                              ii < Zlength(source_words) &&
                              PtrArray::full(
                                begin, Zlength(source_words),
                                candidate_post_memory)
                            which implies
                            ((jj == ii &&
                              i == begin + ii &&
                              j == begin + jj &&
                              j == i &&
                              propagation_ptr_segment(
                                begin, 0, ii,
                                sublist(
                                  0, ii,
                                  candidate_post_memory)) *
                              data_at(
                                begin + ii * sizeof(struct clause_t *),
                                struct clause_t *,
                                Znth(
                                  ii,
                                  candidate_post_memory, 0)) *
                              propagation_ptr_segment(
                                begin, ii + 1,
                                Zlength(source_words),
                                sublist(ii + 1,
                                  Zlength(source_words),
                                  candidate_post_memory))) ||
                             (jj < ii &&
                              i == begin + ii &&
                              j == begin + jj &&
                              propagation_ptr_segment(
                                begin, 0, jj,
                                sublist(
                                  0, jj,
                                  candidate_post_memory)) *
                              data_at(
                                begin + jj * sizeof(struct clause_t *),
                                struct clause_t *,
                                Znth(
                                  jj,
                                  candidate_post_memory, 0)) *
                              propagation_ptr_segment(
                                begin, jj + 1, ii,
                                sublist(jj + 1, ii,
                                  candidate_post_memory)) *
                              data_at(
                                begin + ii * sizeof(struct clause_t *),
                                struct clause_t *,
                                Znth(
                                  ii,
                                  candidate_post_memory, 0)) *
                              propagation_ptr_segment(
                                begin, ii + 1,
                                Zlength(source_words),
                                sublist(ii + 1,
                                  Zlength(source_words),
                                  candidate_post_memory))))
                            $ unit_same unit_move
                         */
                        *j = *i;
                        j++;
                        // Clause is unit under assignment:
                        /*@ exists rsn trl,
                              enqueue_input(
                                ms_size(Mscan), watch0, ms_qtail(Mscan),
                                mt_assigns(ms_core(Mscan)),
                                mt_levels(ms_core(Mscan)),
                                ms_reason_words(Mscan),
                                mt_trail(ms_core(Mscan))) &&
                              0 <= ms_size(Mscan) &&
                              ms_size(Mscan) <= ms_cap(Mscan) &&
                              ms_cap(Mscan) <= INT_MAX &&
                              ms_qtail(Mscan) <= ms_cap(Mscan) &&
                              store(&(s->levels), int *, levels_entry) *
                              store(&(s->reasons), clause **, rsn) *
                              store(&(s->trail), lit *, trl) *
                              CharArray::seg(
                                values, 0, ms_size(Mscan),
                                mt_assigns(ms_core(Mscan))) *
                              solver_char_tail(
                                values, ms_size(Mscan), ms_cap(Mscan)) *
                              solver_propagation_scan_core_at(
                                s, Mscan, values, rsn, levels_entry, trl,
                                simp_count, prop_count)
                            which implies
                            enqueue_input(
                              ms_size(Mscan), watch0, ms_qtail(Mscan),
                              mt_assigns(ms_core(Mscan)),
                              mt_levels(ms_core(Mscan)),
                              ms_reason_words(Mscan),
                              mt_trail(ms_core(Mscan))) &&
                            enqueue_state_at(
                              s, values, levels_entry,
                              ms_size(Mscan), ms_cap(Mscan), ms_qtail(Mscan),
                              mt_assigns(ms_core(Mscan)),
                              mt_levels(ms_core(Mscan)),
                              ms_reason_words(Mscan),
                              mt_trail(ms_core(Mscan)),
                              mt_lim(ms_core(Mscan))) *
                            store(&(s->simpdb_props), int, simp_count) *
                            store(&(s->binary), clause *, ms_binary(Mscan)) *
                            solver_binary_rep(Mscan) *
                            store(&(s->stats.propagations), unsigned long long,
                                  prop_count) *
                            store(&(s->stats.inspects), unsigned long long,
                                  stats_inspects(ms_stats(Mscan))) *
                            solver_propagate_frame(s, Mscan)
                         */
                        if (!enqueue(s,lits[0], *i)){
                            confl = *i;
                            /*@ exists conflict_ret,
                                  conflict_ret <= 0 &&
                                  solver_shape(Mscan) &&
                                  msolver_seed_shadow(Mscan) &&
                                  propagation_caller_frame(M0, Mscan) &&
                                  propagation_scan_frontier(
                                    Mentry, Mscan, p) &&
                                  solver_propagation_scan_semantics(
                                    n, F, A_arr, K, Mscan, p, 0,
                                    retained, rest) &&
                                  minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                                  propagation_replacement_scan_inv(
                                    n, Mscan, false_lit,
                                    propagation_normalized_clause(
                                      watch0, false_lit,
                                      clause_contents),
                                    Zlength(
                                      propagation_normalized_clause(
                                        watch0, false_lit,
                                        clause_contents))) &&
                                  rest == cons(scan_current, raw_suffix) &&
                                  confl == scan_current &&
                                  Znth(ii, candidate_post_memory, 0) ==
                                    scan_current &&
                                  false_lit == lit_neg_c(p) &&
                                  clause_lits_pointer(
                                    scan_current, lits) &&
                                  real_watch_pair(
                                    p, clause_contents) &&
                                  0 <= p && p < 2 * n &&
                                  watch0 + false_lit ==
                                    Znth(0, clause_contents, 0) +
                                    Znth(1, clause_contents, 0) &&
                                  simp_count ==
                                    ms_simpdb_props(Mscan) &&
                                  prop_count ==
                                    stats_propagations(ms_stats(Mscan)) &&
                                  clause_db_pair_frame(
                                    ms_prob(Mscan), ms_learnt(Mscan),
                                    scan_current, clause_contents) *
                                  store(lits + 0 * sizeof(int), int,
                                        watch0) *
                                  store(lits + 1 * sizeof(int), int,
                                        false_lit) *
                                  IntArray::seg(
                                    lits, 2, Zlength(clause_contents),
                                    sublist(2, Zlength(clause_contents),
                                            clause_contents)) *
                                  enqueue_post_at(
                                    s, values, levels_entry,
                                    watch0,
                                    Znth(ii, candidate_post_memory, 0),
                                    ms_size(Mscan), ms_cap(Mscan),
                                    ms_qtail(Mscan), conflict_ret,
                                    mt_assigns(ms_core(Mscan)),
                                    mt_levels(ms_core(Mscan)),
                                    ms_reason_words(Mscan),
                                    mt_trail(ms_core(Mscan)),
                                    mt_lim(ms_core(Mscan))) *
                                  store(&(s->qhead), int,
                                    mt_qhead(ms_core(Mscan))) *
                                  store(&(s->simpdb_props), int,
                                    simp_count) *
                                  store(&(s->binary), clause *,
                                    ms_binary(Mscan)) *
                                  solver_binary_rep(Mscan) *
                                  store(&(s->stats.propagations),
                                    unsigned long long, prop_count) *
                                  store(&(s->stats.inspects),
                                    unsigned long long,
                                    stats_inspects(ms_stats(Mscan))) *
                                  solver_propagate_frame(s, Mscan)
                                which implies
                                exists prob_route learnt_route Mroute,
                                  propagation_unit_conflict_ready(
                                    n, F, A_arr, K, Mscan, p,
                                    scan_current, watch0, false_lit,
                                    clause_contents, retained, rest,
                                    prob_route, learnt_route, Mroute) &&
                                  minisat_propagation_reuse_scan(M0, Mroute, p, scan_current, nil) &&
                                  solver_shape(Mroute) &&
                                  msolver_seed_shadow(Mroute) &&
                                  propagation_caller_frame(M0, Mroute) &&
                                  propagation_scan_frontier( Mentry, Mroute, p) &&
                                  ms_wm(Mroute) == ms_wm(Mscan) &&
                                  simp_count ==
                                    ms_simpdb_props(Mroute) &&
                                  prop_count ==
                                    stats_propagations(ms_stats(Mroute)) &&
                                  confl == scan_current &&
                                  clause_db_rep(prob_route) *
                                  clause_db_rep(learnt_route) *
                                  solver_propagation_nonwatch_rest_at(
                                    s, Mroute, values, levels_entry) *
                                  has_permission(&lits)
                             */
                            /*@ Given prob_route learnt_route Mroute */
                            i++;
                            // Copy the remaining watches:
                            /*@ ii <= jj && jj <= ii &&
                                Zlength(candidate_post_memory) ==
                                  Zlength(source_words) &&
                                Znth(ii, candidate_post_memory, 0) ==
                                  scan_current &&
                                propagation_ptr_segment(
                                  begin, 0, ii,
                                  sublist(
                                    0, ii,
                                    candidate_post_memory)) *
                                data_at(
                                  begin + ii * sizeof(struct clause_t *),
                                  struct clause_t *,
                                  Znth(ii, candidate_post_memory, 0)) *
                                propagation_ptr_segment(
                                  begin, ii + 1,
                                  Zlength(source_words),
                                  sublist(ii + 1,
                                    Zlength(source_words),
                                    candidate_post_memory))
                                $ unit_same
                                which implies
                                PtrArray::full(
                                  begin, Zlength(source_words),
                                  replace_Znth(
                                    jj, scan_current,
                                    candidate_post_memory))
                                $ unit_same
                             */
                            /*@ Znth(ii, candidate_post_memory, 0) ==
                                  scan_current &&
                                Zlength(candidate_post_memory) ==
                                  Zlength(source_words) &&
                                propagation_ptr_segment(
                                  begin, 0, jj,
                                  sublist(
                                    0, jj,
                                    candidate_post_memory)) *
                                data_at(
                                  begin + jj * sizeof(struct clause_t *),
                                  struct clause_t *,
                                  Znth(ii, candidate_post_memory, 0)) *
                                propagation_ptr_segment(
                                  begin, jj + 1, ii,
                                  sublist(jj + 1, ii,
                                    candidate_post_memory)) *
                                data_at(
                                  begin + ii * sizeof(struct clause_t *),
                                  struct clause_t *,
                                  Znth(ii, candidate_post_memory, 0)) *
                                propagation_ptr_segment(
                                  begin, ii + 1,
                                  Zlength(source_words),
                                  sublist(ii + 1,
                                    Zlength(source_words),
                                    candidate_post_memory))
                                $ unit_move
                                which implies
                                PtrArray::full(
                                  begin, Zlength(source_words),
                                  replace_Znth(
                                    jj, scan_current,
                                    candidate_post_memory))
                                $ unit_move
                             */

                            /*@ Branch name
                                unit_conflict_copy: 0 <= jj && jj <= ii
                             */
                            /*@ Inv Assert (exists copy_memory copy_src copy_dst,
                                  s == s@pre &&
                                  mt_qhead(ms_core(M0)) < ms_qtail(M0) &&
                                  values == assigns_entry &&
                                  solver_shape(Mroute) &&
                                  msolver_seed_shadow(Mroute) &&
                                  propagation_caller_frame(M0, Mroute) &&
                                  propagation_scan_frontier( Mentry, Mroute, p) &&
                                  propagation_watch_scan_physical(
                                    source_words, retained, moved, rest,
                                    garbage, watch_memory, ii, jj) &&
                                  propagation_unit_conflict_ready(
                                    n, F, A_arr, K, Mscan, p,
                                    scan_current, watch0, false_lit,
                                    clause_contents, retained, rest,
                                    prob_route, learnt_route, Mroute) &&
                                  minisat_propagation_reuse_scan(M0, Mroute, p, scan_current, nil) &&
                                  rest == cons(scan_current, raw_suffix) &&
                                  confl == scan_current &&
                                  endvar == begin + Zlength(source_words) &&
                                  i == begin + copy_src &&
                                  j == begin + copy_dst &&
                                  0 <= copy_dst && copy_dst <= copy_src &&
                                  copy_src <= Zlength(source_words) &&
                                  Zlength(copy_memory) == Zlength(source_words) &&
                                  binary_watch_copy_progress(
                                    watch_memory, raw_prefix,
                                    scan_current, raw_suffix,
                                    ii, jj, copy_src, copy_dst,
                                    copy_memory) &&
                                  ms_wm(Mroute) ==
                                    replace_Znth(p, app(retained, rest), scan_wm) &&
                                  simp_count ==
                                    ms_simpdb_props(Mroute) &&
                                  prop_count ==
                                    stats_propagations(ms_stats(Mroute)) &&
                                  0 <= p && p < 2 * n &&
                                  ws == Vecp::slot(wlists_entry, p) &&
                                  0 <= Zlength(source_words) &&
                                  Zlength(source_words) <= INT_MAX &&
                                  Vecp::rep_ptr(ws, begin, copy_memory) *
                                  solver_wlists_handle(s, wlists_entry) *
                                  VecpArray::missing_i(wlists_entry, p, 0, 2 * n, scan_wm) *
                                  clause_db_rep(prob_route) *
                                  clause_db_rep(learnt_route) *
                                  solver_propagation_nonwatch_rest_at(
                                    s, Mroute, values, levels_entry) *
                                  has_permission(&sig) *
                                  has_permission(&k) *
                                  has_permission(&lits) *
                                  has_permission(&stop)) *
          store(&l_Undef, char, 0) * store(&true, int, 1)
                             */
                            while (i < endvar) {
                                /*@ Given copy_memory copy_src copy_dst */
                                /*@ i == begin + copy_src &&
                                      j == begin + copy_dst &&
                                      0 <= copy_dst &&
                                      copy_dst <= copy_src &&
                                      copy_src < Zlength(source_words) &&
                                      PtrArray::full(
                                        begin, Zlength(source_words),
                                        copy_memory)
                                    which implies
                                    ((copy_dst == copy_src &&
                                      i == begin + copy_src &&
                                      j == begin + copy_dst &&
                                      data_at(
                                        i,
                                        Znth(copy_src,
                                             copy_memory, 0)) *
                                      PtrArray::missing_i(
                                        begin, copy_src, 0,
                                        Zlength(source_words),
                                        copy_memory)) ||
                                     (copy_dst < copy_src &&
                                      i == begin + copy_src &&
                                      j == begin + copy_dst &&
                                      PtrArray::seg(
                                        begin, 0, copy_dst,
                                        sublist(0, copy_dst,
                                          copy_memory)) *
                                      data_at(
                                        j,
                                        Znth(copy_dst,
                                             copy_memory, 0)) *
                                      PtrArray::seg(
                                        begin, copy_dst + 1,
                                        copy_src,
                                        sublist(copy_dst + 1,
                                          copy_src, copy_memory)) *
                                      data_at(
                                        i,
                                        Znth(copy_src,
                                             copy_memory, 0)) *
                                      PtrArray::seg(
                                        begin, copy_src + 1,
                                        Zlength(source_words),
                                        sublist(copy_src + 1,
                                          Zlength(source_words),
                                          copy_memory))))
                                 */
                                *j = *i;
                                j++;
                                i++;
                            }
                        /*@ Given copy_memory copy_src copy_dst */
                        /*@ i >= endvar &&
                                  endvar == begin +
                                    Zlength(source_words) &&
                                  i == begin + copy_src &&
                                  j == begin + copy_dst &&
                                  copy_src <=
                                    Zlength(source_words) &&
                                  binary_watch_copy_progress(
                                    watch_memory, raw_prefix,
                                    scan_current, raw_suffix,
                                    ii, jj, copy_src, copy_dst,
                                    copy_memory) &&
                                  propagation_watch_scan_physical(
                                    source_words, retained, moved, rest,
                                    garbage, watch_memory, ii, jj) &&
                                  propagation_unit_conflict_ready(
                                    n, F, A_arr, K, Mscan, p,
                                    scan_current, watch0, false_lit,
                                    clause_contents, retained, rest,
                                    prob_route, learnt_route, Mroute) &&
                                  minisat_propagation_reuse_scan(M0, Mroute, p, scan_current, nil) &&
                                  confl == scan_current &&
                                  clause_db_rep(prob_route) *
                                  clause_db_rep(learnt_route) *
                                  solver_propagation_nonwatch_rest_at(
                                    s, Mroute, values, levels_entry)
                                which implies
                                exists retained_route garbage_route,
                                  retained_route == app(retained, rest) &&
                                  confl == scan_current &&
                                  i >= endvar &&
                                  endvar == begin + Zlength(source_words) &&
                                  i == begin + copy_src &&
                                  j == begin + copy_dst &&
                                  propagation_unit_conflict_transition(
                                    n, F, A_arr, K, Mscan, p,
                                    scan_current,
                                    prob_route, learnt_route,
                                    retained_route, Mroute) &&
                                  minisat_propagation_reuse_scan(M0, Mroute, p, scan_current, nil) &&
                                  propagation_scan_conflict_step(
                                    source_words, retained, moved, rest,
                                    copy_memory, garbage_route,
                                    retained_route) &&
                                  solver_propagation_scan_semantics(
                                    n, F, A_arr, K, Mroute, p,
                                    confl, retained_route, nil) &&
                                  minisat_propagation_reuse_scan(M0, Mroute, p, confl, nil) &&
                                  propagation_watch_scan_physical(
                                    source_words, retained_route,
                                    moved, nil, garbage_route,
                                    copy_memory,
                                    Zlength(source_words),
                                    Zlength(retained_route)) &&
                                  clause_db_rep(prob_route) *
                                  clause_db_rep(learnt_route) *
                                  solver_propagation_nonwatch_rest_at(
                                    s, Mroute, values, levels_entry) *
                                  has_permission(&false_lit)
                         */
                        /*@ Given retained_route garbage_route */
                        /*@ solver_propagation_nonwatch_rest_at(
                              s, Mroute, values, levels_entry)
                            which implies exists rsn_route trl_route,
                              store(&(s->qhead), int,
                                mt_qhead(ms_core(Mroute))) *
                              store(&(s->qtail), int,
                                ms_qtail(Mroute)) *
                              store(&(s->simpdb_props), int,
                                ms_simpdb_props(Mroute)) *
                              store(&(s->assigns), lbool *, values) *
                              store(&(s->levels), int *, levels_entry) *
                              store(&(s->reasons), clause **,
                                rsn_route) *
                              store(&(s->trail), lit *, trl_route) *
                              CharArray::seg(
                                values, 0, ms_size(Mroute),
                                mt_assigns(ms_core(Mroute))) *
                              solver_char_tail(
                                values, ms_size(Mroute), ms_cap(Mroute)) *
                              IntArray::seg(
                                levels_entry, 0, ms_size(Mroute),
                                mt_levels(ms_core(Mroute))) *
                              solver_int_tail(
                                levels_entry, ms_size(Mroute), ms_cap(Mroute)) *
                              PtrArray::seg(
                                rsn_route, 0, ms_size(Mroute),
                                ms_reason_words(Mroute)) *
                              solver_ptr_tail(
                                rsn_route, ms_size(Mroute), ms_cap(Mroute)) *
                              IntArray::seg(
                                trl_route, 0, ms_qtail(Mroute),
                                mt_trail(ms_core(Mroute))) *
                              solver_int_tail(
                                trl_route, ms_qtail(Mroute), ms_cap(Mroute)) *
                              Veci::rep(
                                &(s->trail_lim),
                                mt_lim(ms_core(Mroute))) *
                              store(&(s->binary), clause *,
                                ms_binary(Mroute)) *
                              solver_binary_rep(Mroute) *
                              store(&(s->stats.propagations),
                                unsigned long long,
                                stats_propagations(ms_stats(Mroute))) *
                              store(&(s->stats.inspects),
                                unsigned long long,
                                stats_inspects(ms_stats(Mroute))) *
                              solver_propagate_frame(s, Mroute)
                         */
                        /*@ Branch name unit_conflict */
                        /*@ Assert (exists Mnext memory_next logical_next,
                                  exists next_wm,
                                  exists retained_next moved_next rest_next garbage_next,
                                  exists ii_next jj_next prop_count_next simp_count_next,
                                  exists rsn_next lvl_next trl_next,
                                  exists Mentry_next source_words_next,
                                  i >= endvar &&
                                  mt_qhead(ms_core(M0)) < ms_qtail(M0) &&
                                  lvl_next == levels_entry &&
                                  s == s@pre &&
                          values == assigns_entry && solver_shape(Mnext) &&
                                  msolver_seed_shadow(Mnext) &&
                                  propagation_caller_frame(M0, Mnext) &&
                                  propagation_scan_frontier( Mentry_next, Mnext, p) &&
                                  solver_propagation_scan_semantics(
                                    n, F, A_arr, K, Mnext, p, confl,
                                    retained_next, rest_next) &&
                                  minisat_propagation_reuse_scan(M0, Mnext, p, confl, rest_next) &&
                                  propagation_watch_scan_physical(
                                    source_words_next, retained_next, moved_next,
                                    rest_next, garbage_next, memory_next,
                                    ii_next, jj_next) &&
                                  logical_next == app(retained_next, rest_next) &&
                                  ms_wm(Mnext) ==
                                    replace_Znth(p, logical_next, next_wm) &&
                                  0 <= p && p < 2 * n &&
                                  ws == Vecp::slot(wlists_entry, p) &&
                                  endvar == begin + Zlength(source_words_next) &&
                                  Zlength(memory_next) == Zlength(source_words_next) &&
                                  i == begin + ii_next &&
                                  j == begin + jj_next &&
                                  0 <= jj_next && jj_next <= ii_next &&
                                  0 <= ii_next &&
                                  ii_next <= Zlength(source_words_next) &&
                                  (ii_next != 0 ||
                                   Mnext == msolver_propagation_scan_begin(
                                     Mentry_next, simp_count_next, prop_count_next)) &&
                                  simp_count_next == ms_simpdb_props(Mnext) &&
                                  prop_count_next == stats_propagations(ms_stats(Mnext)) &&
                                  0 <= Zlength(source_words_next) &&
                                  Zlength(source_words_next) <= INT_MAX &&
                                  Vecp::rep_ptr(ws, begin, memory_next) *
                                  solver_wlists_handle(s, wlists_entry) *
                                  VecpArray::missing_i(wlists_entry, p, 0, 2 * n, next_wm) *
                                  clause_db_rep(ms_prob(Mnext)) *
                                  clause_db_rep(ms_learnt(Mnext)) *
                                  store(&(s->reasons), clause **, rsn_next) *
                                  store(&(s->levels), int *, lvl_next) *
                                  store(&(s->trail), lit *, trl_next) *
                                  CharArray::seg(
                                    values, 0, ms_size(Mnext),
                                    mt_assigns(ms_core(Mnext))) *
                                  solver_char_tail(
                                    values, ms_size(Mnext), ms_cap(Mnext)) *
                                  store(&(s->qhead), int,
                                    mt_qhead(ms_core(Mnext))) *
                                  solver_propagation_scan_core_at(
                                    s, Mnext, values, rsn_next, lvl_next, trl_next,
                                    simp_count_next, prop_count_next) *
                                  has_permission(&(lits)) *
                                  has_permission(&sig) *
                                  has_permission(&k) *
                                  has_permission(&stop) *
                                  has_permission(&false_lit)) *
          store(&l_Undef, char, 0) * store(&true, int, 1)
                         */
                            break;
                        }
                    /*@ ii <= jj && jj <= ii &&
                                Zlength(candidate_post_memory) ==
                                  Zlength(source_words) &&
                                propagation_ptr_segment(
                                  begin, 0, ii,
                                  sublist(
                                    0, ii,
                                    candidate_post_memory)) *
                                data_at(
                                  begin + ii * sizeof(struct clause_t *),
                                  struct clause_t *, scan_current) *
                                propagation_ptr_segment(
                                  begin, ii + 1,
                                  Zlength(source_words),
                                  sublist(ii + 1,
                                    Zlength(source_words),
                                    candidate_post_memory))
                                $ unit_same
                                which implies
                                PtrArray::full(
                                  begin, Zlength(source_words),
                                  replace_Znth(
                                    jj, scan_current,
                                    candidate_post_memory))
                                $ unit_same
                     */
                    /*@ Znth(ii, candidate_post_memory, 0) == scan_current &&
                                Zlength(candidate_post_memory) ==
                                  Zlength(source_words) &&
                                propagation_ptr_segment(
                                  begin, 0, jj,
                                  sublist(
                                    0, jj,
                                    candidate_post_memory)) *
                                data_at(
                                  begin + jj * sizeof(struct clause_t *),
                                  struct clause_t *, scan_current) *
                                propagation_ptr_segment(
                                  begin, jj + 1, ii,
                                  sublist(jj + 1, ii,
                                    candidate_post_memory)) *
                                data_at(
                                  begin + ii * sizeof(struct clause_t *),
                                  struct clause_t *, scan_current) *
                                propagation_ptr_segment(
                                  begin, ii + 1,
                                  Zlength(source_words),
                                  sublist(ii + 1,
                                    Zlength(source_words),
                                    candidate_post_memory))
                                $ unit_move
                                which implies
                                PtrArray::full(
                                  begin, Zlength(source_words),
                                  replace_Znth(
                                    jj, scan_current,
                                    candidate_post_memory))
                                $ unit_move
                     */
                    /*@ Branch join unit_same unit_move with
                                  PtrArray::full(
                                    begin, Zlength(source_words),
                                    replace_Znth(
                                      jj, scan_current,
                                      candidate_post_memory))
                     */
                    /*@ Given Mentry source_words Mscan watch_memory candidate_post_memory
                              logical_words scan_wm
                              retained moved rest garbage ii jj
                              prop_count simp_count scan_current raw_suffix clause_contents
                              watch0 */
                    /*@ exists unit_ret,
                                unit_ret != 0 &&
                                solver_propagation_scan_semantics(
                                  n, F, A_arr, K, Mscan, p, 0,
                                  retained, rest) &&
                                minisat_propagation_reuse_scan(M0, Mscan, p, 0, rest) &&
                                rest ==
                                  cons(scan_current, raw_suffix) &&
                                propagation_watch_scan_physical(
                                  source_words, retained, moved, rest,
                                  garbage, watch_memory, ii, jj) &&
                                candidate_post_memory == watch_memory &&
                                Znth(ii, candidate_post_memory, 0) ==
                                  scan_current &&
                                false_lit == lit_neg_c(p) &&
                                real_watch_pair(
                                  p, clause_contents) &&
                                watch0 + false_lit ==
                                  Znth(0, clause_contents, 0) +
                                  Znth(1, clause_contents, 0) &&
                                propagation_replacement_scan_inv(
                                  n, Mscan, false_lit,
                                  propagation_normalized_clause(
                                    watch0, false_lit, clause_contents),
                                  Zlength(clause_contents)) &&
                                clause_lits_pointer(
                                  scan_current, lits) &&
                                clause_db_pair_frame(
                                  ms_prob(Mscan), ms_learnt(Mscan),
                                  scan_current, clause_contents) *
                                store(
                                  lits + 0 * sizeof(int), int, watch0) *
                                store(
                                  lits + 1 * sizeof(int), int,
                                  false_lit) *
                                IntArray::seg(
                                  lits, 2,
                                  Zlength(clause_contents),
                                  sublist(2,
                                    Zlength(clause_contents),
                                    clause_contents)) *
                                enqueue_post_at(
                                  s, values, levels_entry,
                                  watch0,
                                  Znth(ii, candidate_post_memory, 0),
                                  ms_size(Mscan), ms_cap(Mscan),
                                  ms_qtail(Mscan), unit_ret,
                                  mt_assigns(ms_core(Mscan)),
                                  mt_levels(ms_core(Mscan)),
                                  ms_reason_words(Mscan),
                                  mt_trail(ms_core(Mscan)),
                                  mt_lim(ms_core(Mscan)))
                              $ unnamed
                              which implies
                              exists prob_route learnt_route Mroute,
                                exists retained_route rest_route,
                                exists garbage_route memory_route,
                                db_pair_lits_update(
                                  ms_prob(Mscan), ms_learnt(Mscan),
                                  scan_current, clause_contents,
                                  propagation_normalized_clause(
                                    watch0, false_lit,
                                    clause_contents),
                                  prob_route, learnt_route) &&
                                retained_route ==
                                  app(retained,
                                    cons(scan_current, nil)) &&
                                rest_route == raw_suffix &&
                                propagation_unit_success_transition(
                                  n, F, A_arr, K, Mscan, p,
                                  watch0, scan_current,
                                  propagation_normalized_clause(
                                    watch0, false_lit,
                                    clause_contents),
                                  prob_route, learnt_route,
                                  retained_route, rest_route,
                                  Mroute) &&
                                minisat_propagation_reuse_scan(M0, Mroute, p, 0, rest_route) &&
                                propagation_scan_keep_step(
                                  source_words, retained, moved, rest,
                                  watch_memory, ii, jj,
                                  scan_current, retained_route,
                                  rest_route, garbage_route,
                                  memory_route) &&
                                clause_db_rep(prob_route) *
                                clause_db_rep(learnt_route) *
                                enqueue_post_at(
                                  s, values, levels_entry,
                                  watch0, scan_current,
                                  ms_size(Mscan), ms_cap(Mscan),
                                  ms_qtail(Mscan), 1,
                                  mt_assigns(ms_core(Mscan)),
                                  mt_levels(ms_core(Mscan)),
                                  ms_reason_words(Mscan),
                                  mt_trail(ms_core(Mscan)),
                                  mt_lim(ms_core(Mscan))) *
                                has_permission(&lits)
                     */
                    /*@ Given prob_route learnt_route Mroute */
                    /*@ Branch name unit_success */

                }
            }
        next:
            i++;
        /*@ Assert (exists Mnext memory_next logical_next,
                  exists next_wm,
                  exists retained_next moved_next rest_next garbage_next,
                  exists ii_next jj_next prop_count_next simp_count_next,
                  exists rsn_next lvl_next trl_next,
                  exists Mentry_next source_words_next,
                  lvl_next == levels_entry &&
                  mt_qhead(ms_core(M0)) < ms_qtail(M0) &&
                  s == s@pre &&
          values == assigns_entry && solver_shape(Mnext) &&
                  msolver_seed_shadow(Mnext) &&
                  propagation_caller_frame(M0, Mnext) &&
                  propagation_scan_frontier( Mentry_next, Mnext, p) &&
                  solver_propagation_scan_semantics(
                    n, F, A_arr, K, Mnext, p, confl,
                    retained_next, rest_next) &&
                  minisat_propagation_reuse_scan(M0, Mnext, p, confl, rest_next) &&
                  propagation_watch_scan_physical(
                    source_words_next, retained_next, moved_next,
                    rest_next, garbage_next, memory_next,
                    ii_next, jj_next) &&
                  logical_next == app(retained_next, rest_next) &&
                  ms_wm(Mnext) ==
                    replace_Znth(p, logical_next, next_wm) &&
                  0 <= p && p < 2 * n &&
                  ws == Vecp::slot(wlists_entry, p) &&
                  endvar == begin + Zlength(source_words_next) &&
                  Zlength(memory_next) == Zlength(source_words_next) &&
                  i == begin + ii_next &&
                  j == begin + jj_next &&
                  0 <= jj_next && jj_next <= ii_next &&
                  0 <= ii_next &&
                  ii_next <= Zlength(source_words_next) &&
                  (ii_next != 0 ||
                   Mnext == msolver_propagation_scan_begin(
                     Mentry_next, simp_count_next, prop_count_next)) &&
                  simp_count_next == ms_simpdb_props(Mnext) &&
                  prop_count_next == stats_propagations(ms_stats(Mnext)) &&
                  0 <= Zlength(source_words_next) &&
                  Zlength(source_words_next) <= INT_MAX &&
                  Vecp::rep_ptr(ws, begin, memory_next) *
                  solver_wlists_handle(s, wlists_entry) *
                  VecpArray::missing_i(wlists_entry, p, 0, 2 * n, next_wm) *
                  clause_db_rep(ms_prob(Mnext)) *
                  clause_db_rep(ms_learnt(Mnext)) *
                  store(&(s->reasons), clause **, rsn_next) *
                  store(&(s->levels), int *, lvl_next) *
                  store(&(s->trail), lit *, trl_next) *
                  CharArray::seg(
                    values, 0, ms_size(Mnext),
                    mt_assigns(ms_core(Mnext))) *
                  solver_char_tail(
                    values, ms_size(Mnext), ms_cap(Mnext)) *
                  store(&(s->qhead), int,
                    mt_qhead(ms_core(Mnext))) *
                  solver_propagation_scan_core_at(
                    s, Mnext, values, rsn_next, lvl_next, trl_next,
                    simp_count_next, prop_count_next) *
                  has_permission(&(lits))) *
          store(&l_Undef, char, 0) * store(&true, int, 1)
         */
        }

        /*@ Branch join binary_conflict unit_conflict unnamed with
            Assert (exists Mscan watch_memory logical_words,
              exists scan_wm,
              exists retained moved rest garbage,
              exists ii jj prop_count simp_count,
              exists rsn_scan trl_scan Mentry source_words,
              i >= endvar &&
              s == s@pre &&
              mt_qhead(ms_core(M0)) < ms_qtail(M0) &&
          values == assigns_entry &&
              solver_shape(Mscan) &&
              msolver_seed_shadow(Mscan) &&
              propagation_caller_frame(M0, Mscan) &&
              propagation_scan_frontier(Mentry, Mscan, p) &&
              solver_propagation_scan_semantics(
                n, F, A_arr, K, Mscan, p, confl, retained, rest) &&
              minisat_propagation_reuse_scan(M0, Mscan, p, confl, rest) &&
              propagation_watch_scan_physical(
                source_words, retained, moved, rest, garbage,
                watch_memory, ii, jj) &&
              logical_words == app(retained, rest) &&
              ms_wm(Mscan) ==
                replace_Znth(p, logical_words, scan_wm) &&
              0 <= p && p < 2 * n &&
              ws == Vecp::slot(wlists_entry, p) &&
              endvar == begin + Zlength(source_words) &&
              Zlength(watch_memory) == Zlength(source_words) &&
              i == begin + ii && j == begin + jj &&
              0 <= jj && jj <= ii &&
              0 <= ii && ii <= Zlength(source_words) &&
              (ii != 0 ||
               Mscan == msolver_propagation_scan_begin(
                      Mentry, simp_count, prop_count)) &&
              simp_count == ms_simpdb_props(Mscan) &&
              prop_count == stats_propagations(ms_stats(Mscan)) &&
              0 <= Zlength(source_words) &&
              Zlength(source_words) <= INT_MAX &&
              Vecp::rep_ptr(ws, begin, watch_memory) *
              solver_wlists_handle(s, wlists_entry) *
              VecpArray::missing_i(wlists_entry, p, 0, 2 * n, scan_wm) *
              clause_db_rep(ms_prob(Mscan)) *
              clause_db_rep(ms_learnt(Mscan)) *
              CharArray::seg(
                values, 0, ms_size(Mscan),
                mt_assigns(ms_core(Mscan))) *
              solver_char_tail(
                values, ms_size(Mscan), ms_cap(Mscan)) *
              store(&(s->reasons), clause **, rsn_scan) *
              store(&(s->levels), int *, levels_entry) *
              store(&(s->trail), lit *, trl_scan) *
              PtrArray::seg(
                rsn_scan, 0, ms_size(Mscan),
                ms_reason_words(Mscan)) *
              solver_ptr_tail(
                rsn_scan, ms_size(Mscan), ms_cap(Mscan)) *
              IntArray::seg(
                levels_entry, 0, ms_size(Mscan),
                mt_levels(ms_core(Mscan))) *
              solver_int_tail(
                levels_entry, ms_size(Mscan), ms_cap(Mscan)) *
              IntArray::seg(
                trl_scan, 0, ms_qtail(Mscan),
                mt_trail(ms_core(Mscan))) *
              solver_int_tail(
                trl_scan, ms_qtail(Mscan), ms_cap(Mscan)) *
              Veci::rep(
                &(s->trail_lim), mt_lim(ms_core(Mscan))) *
              store(&(s->qhead), int,
                    mt_qhead(ms_core(Mscan))) *
              store(&(s->qtail), int, ms_qtail(Mscan)) *
              store(&(s->simpdb_props), int, simp_count) *
              store(&(s->assigns), lbool *, values) *
              store(&(s->binary), clause *, ms_binary(Mscan)) *
              solver_binary_rep(Mscan) *
              store(&(s->stats.propagations),
                    unsigned long long, prop_count) *
              store(&(s->stats.inspects), unsigned long long,
                    stats_inspects(ms_stats(Mscan))) *
              solver_propagate_frame(s, Mscan) *
              has_permission(&(lits))) *
          store(&l_Undef, char, 0) * store(&true, int, 1)
         */

        /*@ Given Mscan watch_memory logical_words
                  scan_wm
                  retained moved rest garbage
                  ii jj prop_count simp_count
                  rsn_scan trl_scan
                  Mentry source_words */

        /*@ i >= endvar &&
              solver_shape(Mscan) &&
              msolver_seed_shadow(Mscan) &&
              propagation_caller_frame(M0, Mscan) &&
              propagation_scan_frontier(Mentry, Mscan, p) &&
              solver_propagation_scan_semantics(
                n, F, A_arr, K, Mscan, p, confl,
                retained, rest) &&
              minisat_propagation_reuse_scan(M0, Mscan, p, confl, rest) &&
              propagation_watch_scan_physical(
                source_words, retained, moved,
                rest, garbage, watch_memory,
                ii, jj) &&
              logical_words == app(retained, rest) &&
              ms_wm(Mscan) ==
                replace_Znth(p, logical_words, scan_wm) &&
              0 <= p && p < 2 * n &&
              Vecp::slot(wlists_entry, p) <= ws && ws <= Vecp::slot(wlists_entry, p) &&
              endvar == begin + Zlength(source_words) &&
              i == begin + ii &&
              j == begin + jj &&
              0 <= Zlength(source_words) &&
              Zlength(watch_memory) == Zlength(source_words) &&
              Zlength(source_words) <= INT_MAX &&
              solver_wlists_handle(s, wlists_entry) *
              VecpArray::missing_i(wlists_entry, p, 0, 2 * n, scan_wm) *
              Vecp::rep_ptr(ws, begin, watch_memory)
            which implies
              solver_shape(Mscan) &&
              msolver_seed_shadow(Mscan) &&
              propagation_caller_frame(M0, Mscan) &&
              propagation_scan_frontier(Mentry, Mscan, p) &&
              solver_propagation_scan_semantics(
                n, F, A_arr, K, Mscan, p, confl,
                retained, nil) &&
              minisat_propagation_reuse_scan(M0, Mscan, p, confl, nil) &&
              propagation_watch_scan_physical(
                source_words, retained, moved,
                nil, garbage, watch_memory,
                ii, jj) &&
              ii == Zlength(source_words) &&
              Zlength(watch_memory) == Zlength(source_words) &&
              jj == Zlength(retained) &&
              ms_wm(Mscan) ==
                replace_Znth(p, retained, scan_wm) &&
              0 <= p && p < 2 * n &&
              ws == Vecp::slot(wlists_entry, p) &&
              endvar == begin + Zlength(source_words) &&
              i == endvar &&
              j == begin + jj &&
              solver_wlists_handle(s, wlists_entry) *
              VecpArray::missing_i(wlists_entry, p, 0, 2 * n, scan_wm) *
              Vecp::rep_ptr(ws, begin, watch_memory)
         */
        s->stats.inspects += j - (clause**)vecp_begin(ws);
        /*@ j == begin + jj
            which implies
            j - begin == jj
         */
        vecp_resize(ws,j - (clause**)vecp_begin(ws));
    /*@ Assert (exists Mfinish rsn_finish lvl_finish trl_finish,
              lvl_finish == levels_entry &&
              mt_qhead(ms_core(M0)) < ms_qtail(M0) &&
              s == s@pre &&
          values == assigns_entry &&
              solver_shape(Mfinish) &&
              msolver_seed_shadow(Mfinish) &&
              ((confl == 0 &&
                propagation_scan_live_finalize(
                  n, F, A_arr, K, M0, Mscan, p,
                  jj, retained, Mfinish)) ||
               (confl != 0 &&
                propagation_scan_conflict_finalize(
                  n, F, A_arr, K, M0, Mscan, p, confl,
                  jj, retained, Mfinish))) &&
              solver_propagation_loop_inv(
                n, F, A_arr, K, M0, Mfinish, confl) &&
              minisat_propagation_reuse_loop(n, M0, Mfinish, confl) &&
              sublist(0, jj, watch_memory) ==
                retained &&
              ms_wm(Mfinish) ==
                replace_Znth(p, retained, scan_wm) &&
              0 <= mt_qhead(ms_core(Mfinish)) &&
              mt_qhead(ms_core(Mfinish)) <= ms_qtail(Mfinish) &&
              ms_qtail(Mfinish) <= ms_size(Mfinish) &&
              ms_size(Mfinish) <= ms_cap(Mfinish) &&
              Zlength(mt_trail(ms_core(Mfinish))) ==
                ms_qtail(Mfinish) &&
              store(&(s->qhead), int,
                    mt_qhead(ms_core(Mfinish))) *
              store(&(s->qtail), int, ms_qtail(Mfinish)) *
              store(&(s->simpdb_props), int,
                    ms_simpdb_props(Mfinish)) *
              store(&(s->wlists), vecp *, wlists_entry) *
              store(&(s->assigns), lbool *, values) *
              store(&(s->reasons), clause **, rsn_finish) *
              store(&(s->levels), int *, lvl_finish) *
              store(&(s->trail), lit *, trl_finish) *
              store(&(s->binary), clause *,
                    ms_binary(Mfinish)) *
              CharArray::seg(
                values, 0, ms_size(Mfinish),
                mt_assigns(ms_core(Mfinish))) *
              solver_char_tail(
                values, ms_size(Mfinish), ms_cap(Mfinish)) *
              PtrArray::seg(
                rsn_finish, 0, ms_size(Mfinish),
                ms_reason_words(Mfinish)) *
              solver_ptr_tail(
                rsn_finish, ms_size(Mfinish), ms_cap(Mfinish)) *
              IntArray::seg(
                lvl_finish, 0, ms_size(Mfinish),
                mt_levels(ms_core(Mfinish))) *
              solver_int_tail(
                lvl_finish, ms_size(Mfinish), ms_cap(Mfinish)) *
              IntArray::seg(
                trl_finish, 0, ms_qtail(Mfinish),
                mt_trail(ms_core(Mfinish))) *
              solver_int_tail(
                trl_finish, ms_qtail(Mfinish), ms_cap(Mfinish)) *
              Veci::rep(
                &(s->trail_lim), mt_lim(ms_core(Mfinish))) *
              wlists_rep(
                wlists_entry, ms_size(Mfinish),
                ms_wm(Mfinish)) *
              clause_db_rep(ms_prob(Mfinish)) *
              clause_db_rep(ms_learnt(Mfinish)) *
              solver_binary_rep(Mfinish) *
              store(&(s->stats.propagations),
                    unsigned long long,
                    stats_propagations(ms_stats(Mfinish))) *
              store(&(s->stats.inspects),
                    unsigned long long,
                    stats_inspects(ms_stats(Mfinish))) *
              solver_propagate_frame(s, Mfinish) *
              has_permission(&(lits)) *
              has_permission(&begin) * has_permission(&endvar) *
              has_permission(&i) * has_permission(&j) *
              has_permission(&ws)) *
          store(&l_Undef, char, 0) * store(&true, int, 1)
     */
    }

    return confl;
}
