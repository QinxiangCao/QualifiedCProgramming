#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq
      (EditZeroPrefix : list Z -> Z -> Prop)
      (EditZeroFull : Z -> list Z -> Prop)
      (EditSegmentPrefix : list Z -> Z -> list Z -> Prop)
      (EditCountsForPrefix : list Z -> list Z -> Z -> Z -> list Z -> list Z -> Prop)
      (EditBuildState : list Z -> list Z -> Z -> Z -> list Z -> list Z -> list Z -> Prop)
      (EditScratchCountsBound : Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (EditGreedyPrefixState : list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (EditGreedyCurrentAvailability : Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (EditGreedyCompletedMaximumFacts : list Z -> list Z -> list Z -> list Z -> Z -> Prop)
      (EditGreedyCompletedStateFacts : list Z -> list Z -> list Z -> list Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (EditStringsMaximum : list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_lib */

int max_edit_string_matches(int *s1, int *s2, int *t1, int *t2, int n,
                            int *seg1, int *seg2,
                            int *cnt10, int *cnt11,
                            int *cnt20, int *cnt21)
/*@ With (s1_l : list Z) (s2_l : list Z) (t1_l : list Z) (t2_l : list Z)
    Require
      1 <= n && n <= 100000 &&
      Zlength(s1_l) == n &&
      Zlength(s2_l) == n &&
      Zlength(t1_l) == n &&
      Zlength(t2_l) == n &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n) &&
      IntArray::full(s1, n, s1_l) *
      IntArray::full(s2, n, s2_l) *
      IntArray::full(t1, n, t1_l) *
      IntArray::full(t2, n, t2_l) *
      IntArray::undef_full(seg1, n) *
      IntArray::undef_full(seg2, n) *
      IntArray::undef_full(cnt10, n) *
      IntArray::undef_full(cnt11, n) *
      IntArray::undef_full(cnt20, n) *
      IntArray::undef_full(cnt21, n) &&
      (forall (idx : Z), (0 <= idx && idx < n) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
    Ensure
      exists seg1_l seg2_l cnt10_l cnt11_l cnt20_l cnt21_l,
      0 <= __return && __return <= n &&
      EditStringsMaximum(s1_l, s2_l, t1_l, t2_l, n, __return) &&
      IntArray::full(s1, n, s1_l) *
      IntArray::full(s2, n, s2_l) *
      IntArray::full(t1, n, t1_l) *
      IntArray::full(t2, n, t2_l) *
      IntArray::full(seg1, n, seg1_l) *
      IntArray::full(seg2, n, seg2_l) *
      IntArray::full(cnt10, n, cnt10_l) *
      IntArray::full(cnt11, n, cnt11_l) *
      IntArray::full(cnt20, n, cnt20_l) *
      IntArray::full(cnt21, n, cnt21_l)
 */
{
  /*@ Inv Assert
      exists c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      0 <= i && i <= n@pre &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditZeroPrefix(c10, i) &&
      EditZeroPrefix(c11, i) &&
      EditZeroPrefix(c20, i) &&
      EditZeroPrefix(c21, i) &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::undef_full(seg1@pre, n@pre) *
      IntArray::undef_full(seg2@pre, n@pre) *
      IntArray::seg(cnt10@pre, 0, i, c10) *
      IntArray::undef_seg(cnt10@pre, i, n@pre) *
      IntArray::seg(cnt11@pre, 0, i, c11) *
      IntArray::undef_seg(cnt11@pre, i, n@pre) *
      IntArray::seg(cnt20@pre, 0, i, c20) *
      IntArray::undef_seg(cnt20@pre, i, n@pre) *
      IntArray::seg(cnt21@pre, 0, i, c21) *
      IntArray::undef_seg(cnt21@pre, i, n@pre) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
   */
  for (int i = 0; i < n; ++i) {
    cnt10[i] = 0;
    cnt11[i] = 0;
    cnt20[i] = 0;
    cnt21[i] = 0;
    /*@ Assert
      exists c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      0 <= i && i < n@pre &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditZeroPrefix(c10, i + 1) &&
      EditZeroPrefix(c11, i + 1) &&
      EditZeroPrefix(c20, i + 1) &&
      EditZeroPrefix(c21, i + 1) &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::undef_full(seg1@pre, n@pre) *
      IntArray::undef_full(seg2@pre, n@pre) *
      IntArray::seg(cnt10@pre, 0, i + 1, c10) *
      IntArray::undef_seg(cnt10@pre, i + 1, n@pre) *
      IntArray::seg(cnt11@pre, 0, i + 1, c11) *
      IntArray::undef_seg(cnt11@pre, i + 1, n@pre) *
      IntArray::seg(cnt20@pre, 0, i + 1, c20) *
      IntArray::undef_seg(cnt20@pre, i + 1, n@pre) *
      IntArray::seg(cnt21@pre, 0, i + 1, c21) *
      IntArray::undef_seg(cnt21@pre, i + 1, n@pre) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
     */
  }

  /*@ Assert
      exists c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditZeroFull(n@pre, c10) &&
      EditZeroFull(n@pre, c11) &&
      EditZeroFull(n@pre, c20) &&
      EditZeroFull(n@pre, c21) &&
      EditScratchCountsBound(n@pre, c10, c11, c20, c21) &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::undef_full(seg1@pre, n@pre) *
      IntArray::undef_full(seg2@pre, n@pre) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
   */

  if (n <= 0) {
    return 0;
  }

  seg1[0] = 0;
  /*@ Assert
      exists sg1 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      Zlength(sg1) == 1 &&
      sg1[0] == 0 &&
      EditZeroFull(n@pre, c10) &&
      EditZeroFull(n@pre, c11) &&
      EditZeroFull(n@pre, c20) &&
      EditZeroFull(n@pre, c21) &&
      EditScratchCountsBound(n@pre, c10, c11, c20, c21) &&
      0 <= c10[0] && c10[0] <= n@pre &&
      0 <= c11[0] && c11[0] <= n@pre &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::seg(seg1@pre, 0, 1, sg1) *
      IntArray::undef_seg(seg1@pre, 1, n@pre) *
      IntArray::undef_full(seg2@pre, n@pre) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
   */
  if (s1[0] == 0) {
    cnt10[0]++;
  } else {
    cnt11[0]++;
  }
  /*@ Assert
      exists sg1 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditBuildState(s1_l, t1_l, n@pre, 1, sg1, c10, c11) &&
      EditZeroFull(n@pre, c20) &&
      EditZeroFull(n@pre, c21) &&
      EditScratchCountsBound(n@pre, c10, c11, c20, c21) &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::seg(seg1@pre, 0, 1, sg1) *
      IntArray::undef_seg(seg1@pre, 1, n@pre) *
      IntArray::undef_full(seg2@pre, n@pre) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
   */
  /*@ Inv Assert
      exists sg1 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= i && i <= n@pre &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditBuildState(s1_l, t1_l, n@pre, i, sg1, c10, c11) &&
      EditZeroFull(n@pre, c20) &&
      EditZeroFull(n@pre, c21) &&
      EditScratchCountsBound(n@pre, c10, c11, c20, c21) &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::seg(seg1@pre, 0, i, sg1) *
      IntArray::undef_seg(seg1@pre, i, n@pre) *
      IntArray::undef_full(seg2@pre, n@pre) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
   */
  for (int i = 1; i < n; ++i) {
    if (t1[i - 1] == 1 && t1[i] == 1) {
      seg1[i] = seg1[i - 1];
    } else {
      seg1[i] = i;
    }
    /*@ Assert
      exists sg1 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= i && i < n@pre &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditSegmentPrefix(t1_l, i + 1, sg1) &&
      EditCountsForPrefix(s1_l, t1_l, n@pre, i, c10, c11) &&
      EditZeroFull(n@pre, c20) &&
      EditZeroFull(n@pre, c21) &&
      EditScratchCountsBound(n@pre, c10, c11, c20, c21) &&
      0 <= sg1[i] && sg1[i] < n@pre &&
      0 <= c10[sg1[i]] && c10[sg1[i]] <= n@pre &&
      0 <= c11[sg1[i]] && c11[sg1[i]] <= n@pre &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::seg(seg1@pre, 0, i + 1, sg1) *
      IntArray::undef_seg(seg1@pre, i + 1, n@pre) *
      IntArray::undef_full(seg2@pre, n@pre) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
     */
    int block1 = seg1[i];
    /*@ Assert
      exists sg1 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      block1 == sg1[i] &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= i && i < n@pre &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditSegmentPrefix(t1_l, i + 1, sg1) &&
      EditCountsForPrefix(s1_l, t1_l, n@pre, i, c10, c11) &&
      EditZeroFull(n@pre, c20) &&
      EditZeroFull(n@pre, c21) &&
      EditScratchCountsBound(n@pre, c10, c11, c20, c21) &&
      0 <= block1 && block1 < n@pre &&
      0 <= c10[block1] && c10[block1] <= n@pre &&
      0 <= c11[block1] && c11[block1] <= n@pre &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::seg(seg1@pre, 0, i + 1, sg1) *
      IntArray::undef_seg(seg1@pre, i + 1, n@pre) *
      IntArray::undef_full(seg2@pre, n@pre) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
     */
    if (s1[i] == 0) {
      cnt10[block1]++;
    } else {
      cnt11[block1]++;
    }
    /*@ Assert
      exists sg1 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      block1 == sg1[i] &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= i && i < n@pre &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditBuildState(s1_l, t1_l, n@pre, i + 1, sg1, c10, c11) &&
      EditZeroFull(n@pre, c20) &&
      EditZeroFull(n@pre, c21) &&
      EditScratchCountsBound(n@pre, c10, c11, c20, c21) &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::seg(seg1@pre, 0, i + 1, sg1) *
      IntArray::undef_seg(seg1@pre, i + 1, n@pre) *
      IntArray::undef_full(seg2@pre, n@pre) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
     */
  }

  /*@ Assert
      exists sg1 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditBuildState(s1_l, t1_l, n@pre, n@pre, sg1, c10, c11) &&
      EditZeroFull(n@pre, c20) &&
      EditZeroFull(n@pre, c21) &&
      EditScratchCountsBound(n@pre, c10, c11, c20, c21) &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::full(seg1@pre, n@pre, sg1) *
      IntArray::undef_full(seg2@pre, n@pre) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
   */

  seg2[0] = 0;
  /*@ Assert
      exists sg1 sg2 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      Zlength(sg2) == 1 &&
      sg2[0] == 0 &&
      EditBuildState(s1_l, t1_l, n@pre, n@pre, sg1, c10, c11) &&
      EditZeroFull(n@pre, c20) &&
      EditZeroFull(n@pre, c21) &&
      EditScratchCountsBound(n@pre, c10, c11, c20, c21) &&
      0 <= c20[0] && c20[0] <= n@pre &&
      0 <= c21[0] && c21[0] <= n@pre &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::full(seg1@pre, n@pre, sg1) *
      IntArray::seg(seg2@pre, 0, 1, sg2) *
      IntArray::undef_seg(seg2@pre, 1, n@pre) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
   */
  if (s2[0] == 0) {
    cnt20[0]++;
  } else {
    cnt21[0]++;
  }
  /*@ Assert
      exists sg1 sg2 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditBuildState(s1_l, t1_l, n@pre, n@pre, sg1, c10, c11) &&
      EditBuildState(s2_l, t2_l, n@pre, 1, sg2, c20, c21) &&
      EditScratchCountsBound(n@pre, c10, c11, c20, c21) &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::full(seg1@pre, n@pre, sg1) *
      IntArray::seg(seg2@pre, 0, 1, sg2) *
      IntArray::undef_seg(seg2@pre, 1, n@pre) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
   */
  /*@ Inv Assert
      exists sg1 sg2 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= i && i <= n@pre &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditBuildState(s1_l, t1_l, n@pre, n@pre, sg1, c10, c11) &&
      EditBuildState(s2_l, t2_l, n@pre, i, sg2, c20, c21) &&
      EditScratchCountsBound(n@pre, c10, c11, c20, c21) &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::full(seg1@pre, n@pre, sg1) *
      IntArray::seg(seg2@pre, 0, i, sg2) *
      IntArray::undef_seg(seg2@pre, i, n@pre) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
   */
  for (int i = 1; i < n; ++i) {
    if (t2[i - 1] == 1 && t2[i] == 1) {
      seg2[i] = seg2[i - 1];
    } else {
      seg2[i] = i;
    }
    /*@ Assert
      exists sg1 sg2 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= i && i < n@pre &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditBuildState(s1_l, t1_l, n@pre, n@pre, sg1, c10, c11) &&
      EditSegmentPrefix(t2_l, i + 1, sg2) &&
      EditCountsForPrefix(s2_l, t2_l, n@pre, i, c20, c21) &&
      EditScratchCountsBound(n@pre, c10, c11, c20, c21) &&
      0 <= sg2[i] && sg2[i] < n@pre &&
      0 <= c20[sg2[i]] && c20[sg2[i]] <= n@pre &&
      0 <= c21[sg2[i]] && c21[sg2[i]] <= n@pre &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::full(seg1@pre, n@pre, sg1) *
      IntArray::seg(seg2@pre, 0, i + 1, sg2) *
      IntArray::undef_seg(seg2@pre, i + 1, n@pre) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
     */
    int block2 = seg2[i];
    /*@ Assert
      exists sg1 sg2 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      block2 == sg2[i] &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= i && i < n@pre &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditBuildState(s1_l, t1_l, n@pre, n@pre, sg1, c10, c11) &&
      EditSegmentPrefix(t2_l, i + 1, sg2) &&
      EditCountsForPrefix(s2_l, t2_l, n@pre, i, c20, c21) &&
      EditScratchCountsBound(n@pre, c10, c11, c20, c21) &&
      0 <= block2 && block2 < n@pre &&
      0 <= c20[block2] && c20[block2] <= n@pre &&
      0 <= c21[block2] && c21[block2] <= n@pre &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::full(seg1@pre, n@pre, sg1) *
      IntArray::seg(seg2@pre, 0, i + 1, sg2) *
      IntArray::undef_seg(seg2@pre, i + 1, n@pre) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
     */
    if (s2[i] == 0) {
      cnt20[block2]++;
    } else {
      cnt21[block2]++;
    }
    /*@ Assert
      exists sg1 sg2 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      block2 == sg2[i] &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= i && i < n@pre &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditBuildState(s1_l, t1_l, n@pre, n@pre, sg1, c10, c11) &&
      EditBuildState(s2_l, t2_l, n@pre, i + 1, sg2, c20, c21) &&
      EditScratchCountsBound(n@pre, c10, c11, c20, c21) &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::full(seg1@pre, n@pre, sg1) *
      IntArray::seg(seg2@pre, 0, i + 1, sg2) *
      IntArray::undef_seg(seg2@pre, i + 1, n@pre) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
     */
  }

  /*@ Assert
      exists sg1 sg2 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditBuildState(s1_l, t1_l, n@pre, n@pre, sg1, c10, c11) &&
      EditBuildState(s2_l, t2_l, n@pre, n@pre, sg2, c20, c21) &&
      EditScratchCountsBound(n@pre, c10, c11, c20, c21) &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::full(seg1@pre, n@pre, sg1) *
      IntArray::full(seg2@pre, n@pre, sg2) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
   */

  int ans = 0;
  /*@ Assert
      exists sg1 sg2 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      ans == 0 &&
      1 <= n@pre && n@pre <= 100000 &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditGreedyPrefixState(s1_l, s2_l, t1_l, t2_l, n@pre, 0, ans, sg1, sg2, c10, c11, c20, c21) &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::full(seg1@pre, n@pre, sg1) *
      IntArray::full(seg2@pre, n@pre, sg2) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
   */
  /*@ Inv Assert
      exists sg1 sg2 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      0 <= i && i <= n@pre &&
      0 <= ans && ans <= i &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditGreedyPrefixState(s1_l, s2_l, t1_l, t2_l, n@pre, i, ans, sg1, sg2, c10, c11, c20, c21) &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::full(seg1@pre, n@pre, sg1) *
      IntArray::full(seg2@pre, n@pre, sg2) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
   */
  for (int i = 0; i < n; ++i) {
    int a = seg1[i];
    int b = seg2[i];
    /*@ Assert
      exists sg1 sg2 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      0 <= i && i < n@pre &&
      0 <= ans && ans <= i &&
      a == sg1[i] &&
      b == sg2[i] &&
      0 <= a && a < n@pre &&
      0 <= b && b < n@pre &&
      0 <= c10[a] && c10[a] <= n@pre &&
      0 <= c11[a] && c11[a] <= n@pre &&
      0 <= c20[b] && c20[b] <= n@pre &&
      0 <= c21[b] && c21[b] <= n@pre &&
      EditGreedyCurrentAvailability(n@pre, i, sg1, sg2, c10, c11, c20, c21) &&
      0 < c10[a] + c11[a] &&
      0 < c20[b] + c21[b] &&
      ans + 1 <= INT_MAX &&
      Zlength(s1_l) == n@pre &&
      Zlength(s2_l) == n@pre &&
      Zlength(t1_l) == n@pre &&
      Zlength(t2_l) == n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditGreedyPrefixState(s1_l, s2_l, t1_l, t2_l, n@pre, i, ans, sg1, sg2, c10, c11, c20, c21) &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::full(seg1@pre, n@pre, sg1) *
      IntArray::full(seg2@pre, n@pre, sg2) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s1_l[idx] && s1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= s2_l[idx] && s2_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t1_l[idx] && t1_l[idx] <= 1)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= t2_l[idx] && t2_l[idx] <= 1))
     */
    if (cnt10[a] > 0 && cnt20[b] > 0) {
      ans++;
      cnt10[a]--;
      cnt20[b]--;
      /*@ Assert
        exists sg1 sg2 c10 c11 c20 c21,
        s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
        seg1 == seg1@pre && seg2 == seg2@pre &&
        cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
        cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
        n == n@pre &&
        1 <= n@pre && n@pre <= 100000 &&
        0 <= i && i < n@pre &&
        0 <= ans && ans <= i + 1 &&
        a == sg1[i] &&
        b == sg2[i] &&
        0 <= a && a < n@pre &&
        0 <= b && b < n@pre &&
        EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
        EditGreedyPrefixState(s1_l, s2_l, t1_l, t2_l, n@pre, i + 1, ans, sg1, sg2, c10, c11, c20, c21) &&
        IntArray::full(s1@pre, n@pre, s1_l) *
        IntArray::full(s2@pre, n@pre, s2_l) *
        IntArray::full(t1@pre, n@pre, t1_l) *
        IntArray::full(t2@pre, n@pre, t2_l) *
        IntArray::full(seg1@pre, n@pre, sg1) *
        IntArray::full(seg2@pre, n@pre, sg2) *
        IntArray::full(cnt10@pre, n@pre, c10) *
        IntArray::full(cnt11@pre, n@pre, c11) *
        IntArray::full(cnt20@pre, n@pre, c20) *
        IntArray::full(cnt21@pre, n@pre, c21)
       */
    } else if (cnt11[a] > 0 && cnt21[b] > 0) {
      ans++;
      cnt11[a]--;
      cnt21[b]--;
      /*@ Assert
        exists sg1 sg2 c10 c11 c20 c21,
        s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
        seg1 == seg1@pre && seg2 == seg2@pre &&
        cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
        cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
        n == n@pre &&
        1 <= n@pre && n@pre <= 100000 &&
        0 <= i && i < n@pre &&
        0 <= ans && ans <= i + 1 &&
        a == sg1[i] &&
        b == sg2[i] &&
        0 <= a && a < n@pre &&
        0 <= b && b < n@pre &&
        EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
        EditGreedyPrefixState(s1_l, s2_l, t1_l, t2_l, n@pre, i + 1, ans, sg1, sg2, c10, c11, c20, c21) &&
        IntArray::full(s1@pre, n@pre, s1_l) *
        IntArray::full(s2@pre, n@pre, s2_l) *
        IntArray::full(t1@pre, n@pre, t1_l) *
        IntArray::full(t2@pre, n@pre, t2_l) *
        IntArray::full(seg1@pre, n@pre, sg1) *
        IntArray::full(seg2@pre, n@pre, sg2) *
        IntArray::full(cnt10@pre, n@pre, c10) *
        IntArray::full(cnt11@pre, n@pre, c11) *
        IntArray::full(cnt20@pre, n@pre, c20) *
        IntArray::full(cnt21@pre, n@pre, c21)
       */
    } else if (cnt10[a] > 0) {
      /*@ Assert
        exists sg1 sg2 c10 c11 c20 c21,
        s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
        seg1 == seg1@pre && seg2 == seg2@pre &&
        cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
        cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
        n == n@pre &&
        1 <= n@pre && n@pre <= 100000 &&
        0 <= i && i < n@pre &&
        0 <= ans && ans <= i &&
        a == sg1[i] &&
        b == sg2[i] &&
	        0 <= a && a < n@pre &&
	        0 <= b && b < n@pre &&
	        (! (0 < c10[a] && 0 < c20[b])) &&
	        (! (0 < c11[a] && 0 < c21[b])) &&
	        0 < c10[a] && c10[a] <= n@pre &&
	        0 < c21[b] && c21[b] <= n@pre &&
	        EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
	        EditGreedyPrefixState(s1_l, s2_l, t1_l, t2_l, n@pre, i, ans, sg1, sg2, c10, c11, c20, c21) &&
        IntArray::full(s1@pre, n@pre, s1_l) *
        IntArray::full(s2@pre, n@pre, s2_l) *
        IntArray::full(t1@pre, n@pre, t1_l) *
        IntArray::full(t2@pre, n@pre, t2_l) *
        IntArray::full(seg1@pre, n@pre, sg1) *
        IntArray::full(seg2@pre, n@pre, sg2) *
        IntArray::full(cnt10@pre, n@pre, c10) *
        IntArray::full(cnt11@pre, n@pre, c11) *
        IntArray::full(cnt20@pre, n@pre, c20) *
        IntArray::full(cnt21@pre, n@pre, c21)
       */
      cnt10[a]--;
      cnt21[b]--;
      /*@ Assert
        exists sg1 sg2 c10 c11 c20 c21,
        s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
        seg1 == seg1@pre && seg2 == seg2@pre &&
        cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
        cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
        n == n@pre &&
        1 <= n@pre && n@pre <= 100000 &&
        0 <= i && i < n@pre &&
        0 <= ans && ans <= i + 1 &&
        a == sg1[i] &&
        b == sg2[i] &&
        0 <= a && a < n@pre &&
        0 <= b && b < n@pre &&
        EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
        EditGreedyPrefixState(s1_l, s2_l, t1_l, t2_l, n@pre, i + 1, ans, sg1, sg2, c10, c11, c20, c21) &&
        IntArray::full(s1@pre, n@pre, s1_l) *
        IntArray::full(s2@pre, n@pre, s2_l) *
        IntArray::full(t1@pre, n@pre, t1_l) *
        IntArray::full(t2@pre, n@pre, t2_l) *
        IntArray::full(seg1@pre, n@pre, sg1) *
        IntArray::full(seg2@pre, n@pre, sg2) *
        IntArray::full(cnt10@pre, n@pre, c10) *
        IntArray::full(cnt11@pre, n@pre, c11) *
        IntArray::full(cnt20@pre, n@pre, c20) *
        IntArray::full(cnt21@pre, n@pre, c21)
       */
    } else {
      /*@ Assert
        exists sg1 sg2 c10 c11 c20 c21,
        s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
        seg1 == seg1@pre && seg2 == seg2@pre &&
        cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
        cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
        n == n@pre &&
        1 <= n@pre && n@pre <= 100000 &&
        0 <= i && i < n@pre &&
        0 <= ans && ans <= i &&
        a == sg1[i] &&
        b == sg2[i] &&
	        0 <= a && a < n@pre &&
	        0 <= b && b < n@pre &&
	        (! (0 < c10[a] && 0 < c20[b])) &&
	        (! (0 < c11[a] && 0 < c21[b])) &&
	        (! (0 < c10[a])) &&
	        0 < c11[a] && c11[a] <= n@pre &&
	        0 < c20[b] && c20[b] <= n@pre &&
	        EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
	        EditGreedyPrefixState(s1_l, s2_l, t1_l, t2_l, n@pre, i, ans, sg1, sg2, c10, c11, c20, c21) &&
        IntArray::full(s1@pre, n@pre, s1_l) *
        IntArray::full(s2@pre, n@pre, s2_l) *
        IntArray::full(t1@pre, n@pre, t1_l) *
        IntArray::full(t2@pre, n@pre, t2_l) *
        IntArray::full(seg1@pre, n@pre, sg1) *
        IntArray::full(seg2@pre, n@pre, sg2) *
        IntArray::full(cnt10@pre, n@pre, c10) *
        IntArray::full(cnt11@pre, n@pre, c11) *
        IntArray::full(cnt20@pre, n@pre, c20) *
        IntArray::full(cnt21@pre, n@pre, c21)
       */
      cnt11[a]--;
      cnt20[b]--;
      /*@ Assert
        exists sg1 sg2 c10 c11 c20 c21,
        s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
        seg1 == seg1@pre && seg2 == seg2@pre &&
        cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
        cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
        n == n@pre &&
        1 <= n@pre && n@pre <= 100000 &&
        0 <= i && i < n@pre &&
        0 <= ans && ans <= i + 1 &&
        a == sg1[i] &&
        b == sg2[i] &&
        0 <= a && a < n@pre &&
        0 <= b && b < n@pre &&
        EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
        EditGreedyPrefixState(s1_l, s2_l, t1_l, t2_l, n@pre, i + 1, ans, sg1, sg2, c10, c11, c20, c21) &&
        IntArray::full(s1@pre, n@pre, s1_l) *
        IntArray::full(s2@pre, n@pre, s2_l) *
        IntArray::full(t1@pre, n@pre, t1_l) *
        IntArray::full(t2@pre, n@pre, t2_l) *
        IntArray::full(seg1@pre, n@pre, sg1) *
        IntArray::full(seg2@pre, n@pre, sg2) *
        IntArray::full(cnt10@pre, n@pre, c10) *
        IntArray::full(cnt11@pre, n@pre, c11) *
        IntArray::full(cnt20@pre, n@pre, c20) *
        IntArray::full(cnt21@pre, n@pre, c21)
       */
    }
  }

  /*@ Assert
      exists sg1 sg2 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      0 <= ans && ans <= n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditGreedyPrefixState(s1_l, s2_l, t1_l, t2_l, n@pre, n@pre, ans, sg1, sg2, c10, c11, c20, c21) &&
      EditGreedyCompletedStateFacts(s1_l, s2_l, t1_l, t2_l, n@pre, ans, sg1, sg2, c10, c11, c20, c21) &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::full(seg1@pre, n@pre, sg1) *
      IntArray::full(seg2@pre, n@pre, sg2) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21)
   */

  /*@ Assert
      exists sg1 sg2 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre &&
      seg1 == seg1@pre && seg2 == seg2@pre &&
      cnt10 == cnt10@pre && cnt11 == cnt11@pre &&
      cnt20 == cnt20@pre && cnt21 == cnt21@pre &&
      n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      0 <= ans && ans <= n@pre &&
      EditGreedyCompletedMaximumFacts(s1_l, s2_l, t1_l, t2_l, n@pre) &&
      EditGreedyPrefixState(s1_l, s2_l, t1_l, t2_l, n@pre, n@pre, ans, sg1, sg2, c10, c11, c20, c21) &&
      EditGreedyCompletedStateFacts(s1_l, s2_l, t1_l, t2_l, n@pre, ans, sg1, sg2, c10, c11, c20, c21) &&
      EditStringsMaximum(s1_l, s2_l, t1_l, t2_l, n@pre, ans) &&
      IntArray::full(s1@pre, n@pre, s1_l) *
      IntArray::full(s2@pre, n@pre, s2_l) *
      IntArray::full(t1@pre, n@pre, t1_l) *
      IntArray::full(t2@pre, n@pre, t2_l) *
      IntArray::full(seg1@pre, n@pre, sg1) *
      IntArray::full(seg2@pre, n@pre, sg2) *
      IntArray::full(cnt10@pre, n@pre, c10) *
      IntArray::full(cnt11@pre, n@pre, c11) *
      IntArray::full(cnt20@pre, n@pre, c20) *
      IntArray::full(cnt21@pre, n@pre, c21)
   */
  return ans;
}
