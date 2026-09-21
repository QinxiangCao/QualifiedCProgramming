/* The solver receives decoded binary digits in int arrays. The public
 * mathematical spec uses source character codes: adding 48 is only the
 * representation bridge, and does not compute the answer. */
/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (eq : {A} -> A -> A -> Prop)
      (map : {A B} -> (A -> B) -> list A -> list B)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (Z::add : Z -> Z -> Z)
      (EditSegmentMeaning : list Z -> Z -> list Z -> Prop)
      (EditCountsMeaning : list Z -> list Z -> Z -> Z -> list Z -> list Z -> Prop)
      (EditBuildMeaning : list Z -> list Z -> Z -> Z -> list Z -> list Z -> list Z -> Prop)
      (EditStringsAnswer : list Z -> list Z -> list Z -> list Z -> Z -> Prop)
      (EditPairMatches : list Z -> list Z -> Z)
      (EditRemainingMatches : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> list Z -> list Z -> list Z -> list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_lib */

int max_edit_string_matches(int *s1, int *s2, int *t1, int *t2, int n)
/*@ With (s1_l s2_l t1_l t2_l : list Z)
    Require 1 <= n && n <= 100000 &&
      Forall(Z::le(0), s1_l) && Forall(Z::ge(1), s1_l) &&
      Forall(Z::le(0), s2_l) && Forall(Z::ge(1), s2_l) &&
      Forall(Z::le(0), t1_l) && Forall(Z::ge(1), t1_l) &&
      Forall(Z::le(0), t2_l) && Forall(Z::ge(1), t2_l) &&
      IntArray::full(s1, n, s1_l) *
      IntArray::full(s2, n, s2_l) *
      IntArray::full(t1, n, t1_l) *
      IntArray::full(t2, n, t2_l)
    Ensure 
      EditStringsAnswer(map(Z::add(48), s1_l), map(Z::add(48), s2_l), map(Z::add(48), t1_l), map(Z::add(48), t2_l), __return) &&
      IntArray::full(s1, n, s1_l) *
      IntArray::full(s2, n, s2_l) *
      IntArray::full(t1, n, t1_l) *
      IntArray::full(t2, n, t2_l)
 */
{
    int seg1[100000];
    int seg2[100000];
    int cnt10[100000];
    int cnt11[100000];
    int cnt20[100000];
    int cnt21[100000];

  /*@ Inv Assert exists c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre && n == n@pre &&
      1 <= n && n <= 100000 && 0 <= i && i <= n &&
      Forall(Z::le(0), s1_l) && Forall(Z::ge(1), s1_l) &&
      Forall(Z::le(0), s2_l) && Forall(Z::ge(1), s2_l) &&
      Forall(Z::le(0), t1_l) && Forall(Z::ge(1), t1_l) &&
      Forall(Z::le(0), t2_l) && Forall(Z::ge(1), t2_l) &&
      Forall(eq(0), c10) && Forall(eq(0), c11) && Forall(eq(0), c20) && Forall(eq(0), c21) &&
      IntArray::full(s1, n, s1_l) *
      IntArray::full(s2, n, s2_l) *
      IntArray::full(t1, n, t1_l) *
      IntArray::full(t2, n, t2_l) *
      IntArray::undef_full(seg1, n) *
      IntArray::undef_seg(seg1, n@pre, 100000) * IntArray::undef_full(seg2, n) *
      IntArray::undef_seg(seg2, n@pre, 100000) *
      IntArray::seg(cnt10, 0, i, c10) * IntArray::undef_seg(cnt10, i, n) *
      IntArray::undef_seg(cnt10, n@pre, 100000) *
      IntArray::seg(cnt11, 0, i, c11) * IntArray::undef_seg(cnt11, i, n) *
      IntArray::undef_seg(cnt11, n@pre, 100000) *
      IntArray::seg(cnt20, 0, i, c20) * IntArray::undef_seg(cnt20, i, n) *
      IntArray::undef_seg(cnt20, n@pre, 100000) *
      IntArray::seg(cnt21, 0, i, c21) * IntArray::undef_seg(cnt21, i, n) *
      IntArray::undef_seg(cnt21, n@pre, 100000)
   */
  for (int i = 0; i < n; ++i) {
    cnt10[i] = 0;
    cnt11[i] = 0;
    cnt20[i] = 0;
    cnt21[i] = 0;
  }
  if (n <= 0) { return 0; }

  seg1[0] = 0;
  if (s1[0] == 0) { cnt10[0]++; } else { cnt11[0]++; }
  /*@ Inv Assert exists sg1 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre && n == n@pre &&
      1 <= n && n <= 100000 && 1 <= i && i <= n &&
      Forall(Z::le(0), s1_l) && Forall(Z::ge(1), s1_l) &&
      Forall(Z::le(0), s2_l) && Forall(Z::ge(1), s2_l) &&
      Forall(Z::le(0), t1_l) && Forall(Z::ge(1), t1_l) &&
      Forall(Z::le(0), t2_l) && Forall(Z::ge(1), t2_l) &&
      Forall(Z::le(0), c10) && Forall(Z::ge(n), c10) &&
      Forall(Z::le(0), c11) && Forall(Z::ge(n), c11) &&
      Forall(Z::le(0), c20) && Forall(Z::ge(n), c20) &&
      Forall(Z::le(0), c21) && Forall(Z::ge(n), c21) &&
      Forall(eq(0), c20) && Forall(eq(0), c21) &&
      EditBuildMeaning(s1_l, t1_l, n, i, sg1, c10, c11) &&
      IntArray::full(s1, n, s1_l) *
      IntArray::full(s2, n, s2_l) *
      IntArray::full(t1, n, t1_l) *
      IntArray::full(t2, n, t2_l) *
      IntArray::seg(seg1, 0, i, sg1) * IntArray::undef_seg(seg1, i, n) *
      IntArray::undef_seg(seg1, n@pre, 100000) * IntArray::undef_full(seg2, n) *
      IntArray::undef_seg(seg2, n@pre, 100000) *
      IntArray::full(cnt10, n, c10) *
      IntArray::undef_seg(cnt10, n@pre, 100000) *
      IntArray::full(cnt11, n, c11) *
      IntArray::undef_seg(cnt11, n@pre, 100000) *
      IntArray::full(cnt20, n, c20) *
      IntArray::undef_seg(cnt20, n@pre, 100000) *
      IntArray::full(cnt21, n, c21) *
      IntArray::undef_seg(cnt21, n@pre, 100000)
   */
  for (int i = 1; i < n; ++i) {
    if (t1[i - 1] == 1 && t1[i] == 1) { seg1[i] = seg1[i - 1]; }
    else { seg1[i] = i; }
    int block1 = seg1[i];
    /*@ Assert exists sg1 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre && n == n@pre &&
      1 <= n && n <= 100000 && 1 <= i && i <= n &&
      Forall(Z::le(0), s1_l) && Forall(Z::ge(1), s1_l) &&
      Forall(Z::le(0), s2_l) && Forall(Z::ge(1), s2_l) &&
      Forall(Z::le(0), t1_l) && Forall(Z::ge(1), t1_l) &&
      Forall(Z::le(0), t2_l) && Forall(Z::ge(1), t2_l) &&
      Forall(Z::le(0), c10) && Forall(Z::ge(n), c10) &&
      Forall(Z::le(0), c11) && Forall(Z::ge(n), c11) &&
      Forall(Z::le(0), c20) && Forall(Z::ge(n), c20) &&
      Forall(Z::le(0), c21) && Forall(Z::ge(n), c21) &&
      Forall(eq(0), c20) && Forall(eq(0), c21) &&
      i < n && 0 <= block1 && block1 <= i &&
      block1 == Znth(i, sg1, 0) &&
      EditSegmentMeaning(t1_l, i + 1, sg1) &&
      EditCountsMeaning(s1_l, t1_l, n, i, c10, c11) &&
      IntArray::full(s1, n, s1_l) *
      IntArray::full(s2, n, s2_l) *
      IntArray::full(t1, n, t1_l) *
      IntArray::full(t2, n, t2_l) *
      IntArray::seg(seg1, 0, i + 1, sg1) * IntArray::undef_seg(seg1, i + 1, n) *
      IntArray::undef_seg(seg1, n@pre, 100000) * IntArray::undef_full(seg2, n) *
      IntArray::undef_seg(seg2, n@pre, 100000) *
      IntArray::full(cnt10, n, c10) *
      IntArray::undef_seg(cnt10, n@pre, 100000) *
      IntArray::full(cnt11, n, c11) *
      IntArray::undef_seg(cnt11, n@pre, 100000) *
      IntArray::full(cnt20, n, c20) *
      IntArray::undef_seg(cnt20, n@pre, 100000) *
      IntArray::full(cnt21, n, c21) *
      IntArray::undef_seg(cnt21, n@pre, 100000)
     */
    if (s1[i] == 0) { cnt10[block1]++; }
    else { cnt11[block1]++; }
  }

  seg2[0] = 0;
  if (s2[0] == 0) { cnt20[0]++; } else { cnt21[0]++; }
  /*@ Inv Assert exists sg1 sg2 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre && n == n@pre &&
      1 <= n && n <= 100000 && 1 <= i && i <= n &&
      Forall(Z::le(0), s1_l) && Forall(Z::ge(1), s1_l) &&
      Forall(Z::le(0), s2_l) && Forall(Z::ge(1), s2_l) &&
      Forall(Z::le(0), t1_l) && Forall(Z::ge(1), t1_l) &&
      Forall(Z::le(0), t2_l) && Forall(Z::ge(1), t2_l) &&
      Forall(Z::le(0), c10) && Forall(Z::ge(n), c10) &&
      Forall(Z::le(0), c11) && Forall(Z::ge(n), c11) &&
      Forall(Z::le(0), c20) && Forall(Z::ge(n), c20) &&
      Forall(Z::le(0), c21) && Forall(Z::ge(n), c21) &&
      EditBuildMeaning(s1_l, t1_l, n, n, sg1, c10, c11) &&
      EditBuildMeaning(s2_l, t2_l, n, i, sg2, c20, c21) &&
      IntArray::full(s1, n, s1_l) *
      IntArray::full(s2, n, s2_l) *
      IntArray::full(t1, n, t1_l) *
      IntArray::full(t2, n, t2_l) *
      IntArray::full(seg1, n, sg1) *
      IntArray::undef_seg(seg1, n@pre, 100000) * IntArray::seg(seg2, 0, i, sg2) * IntArray::undef_seg(seg2, i, n) *
      IntArray::undef_seg(seg2, n@pre, 100000) *
      IntArray::full(cnt10, n, c10) *
      IntArray::undef_seg(cnt10, n@pre, 100000) *
      IntArray::full(cnt11, n, c11) *
      IntArray::undef_seg(cnt11, n@pre, 100000) *
      IntArray::full(cnt20, n, c20) *
      IntArray::undef_seg(cnt20, n@pre, 100000) *
      IntArray::full(cnt21, n, c21) *
      IntArray::undef_seg(cnt21, n@pre, 100000)
   */
  for (int i = 1; i < n; ++i) {
    if (t2[i - 1] == 1 && t2[i] == 1) { seg2[i] = seg2[i - 1]; }
    else { seg2[i] = i; }
    int block2 = seg2[i];
    /*@ Assert exists sg1 sg2 c10 c11 c20 c21,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre && n == n@pre &&
      1 <= n && n <= 100000 && 1 <= i && i <= n &&
      Forall(Z::le(0), s1_l) && Forall(Z::ge(1), s1_l) &&
      Forall(Z::le(0), s2_l) && Forall(Z::ge(1), s2_l) &&
      Forall(Z::le(0), t1_l) && Forall(Z::ge(1), t1_l) &&
      Forall(Z::le(0), t2_l) && Forall(Z::ge(1), t2_l) &&
      Forall(Z::le(0), c10) && Forall(Z::ge(n), c10) &&
      Forall(Z::le(0), c11) && Forall(Z::ge(n), c11) &&
      Forall(Z::le(0), c20) && Forall(Z::ge(n), c20) &&
      Forall(Z::le(0), c21) && Forall(Z::ge(n), c21) &&
      EditBuildMeaning(s1_l, t1_l, n, n, sg1, c10, c11) &&
      i < n && 0 <= block2 && block2 <= i &&
      block2 == Znth(i, sg2, 0) &&
      EditSegmentMeaning(t2_l, i + 1, sg2) &&
      EditCountsMeaning(s2_l, t2_l, n, i, c20, c21) &&
      IntArray::full(s1, n, s1_l) *
      IntArray::full(s2, n, s2_l) *
      IntArray::full(t1, n, t1_l) *
      IntArray::full(t2, n, t2_l) *
      IntArray::full(seg1, n, sg1) *
      IntArray::undef_seg(seg1, n@pre, 100000) * IntArray::seg(seg2, 0, i + 1, sg2) * IntArray::undef_seg(seg2, i + 1, n) *
      IntArray::undef_seg(seg2, n@pre, 100000) *
      IntArray::full(cnt10, n, c10) *
      IntArray::undef_seg(cnt10, n@pre, 100000) *
      IntArray::full(cnt11, n, c11) *
      IntArray::undef_seg(cnt11, n@pre, 100000) *
      IntArray::full(cnt20, n, c20) *
      IntArray::undef_seg(cnt20, n@pre, 100000) *
      IntArray::full(cnt21, n, c21) *
      IntArray::undef_seg(cnt21, n@pre, 100000)
     */
    if (s2[i] == 0) { cnt20[block2]++; }
    else { cnt21[block2]++; }
  }

  int ans = 0;
  /*@ Inv Assert exists sg1 sg2 c10 c11 c20 c21 rest prefix1 prefix2,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre && n == n@pre &&
      1 <= n && n <= 100000 && 0 <= i && i <= n && 0 <= ans && ans <= i &&
      Forall(Z::le(0), s1_l) && Forall(Z::ge(1), s1_l) &&
      Forall(Z::le(0), s2_l) && Forall(Z::ge(1), s2_l) &&
      Forall(Z::le(0), t1_l) && Forall(Z::ge(1), t1_l) &&
      Forall(Z::le(0), t2_l) && Forall(Z::ge(1), t2_l) &&
      Forall(Z::le(0), c10) && Forall(Z::ge(n), c10) &&
      Forall(Z::le(0), c11) && Forall(Z::ge(n), c11) &&
      Forall(Z::le(0), c20) && Forall(Z::ge(n), c20) &&
      Forall(Z::le(0), c21) && Forall(Z::ge(n), c21) &&
      EditSegmentMeaning(t1_l, n, sg1) && EditSegmentMeaning(t2_l, n, sg2) &&
      Zlength(prefix1) == i && Zlength(prefix2) == i && ans == EditPairMatches(prefix1, prefix2) &&
      EditRemainingMatches(s1_l, s2_l, t1_l, t2_l, sg1, sg2, prefix1, prefix2, i, c10, c11, c20, c21, rest) &&
      EditStringsAnswer(map(Z::add(48), s1_l), map(Z::add(48), s2_l), map(Z::add(48), t1_l), map(Z::add(48), t2_l), ans + rest) &&
      IntArray::full(s1, n, s1_l) *
      IntArray::full(s2, n, s2_l) *
      IntArray::full(t1, n, t1_l) *
      IntArray::full(t2, n, t2_l) *
      IntArray::full(seg1, n, sg1) *
      IntArray::undef_seg(seg1, n@pre, 100000) * IntArray::full(seg2, n, sg2) *
      IntArray::undef_seg(seg2, n@pre, 100000) *
      IntArray::full(cnt10, n, c10) *
      IntArray::undef_seg(cnt10, n@pre, 100000) *
      IntArray::full(cnt11, n, c11) *
      IntArray::undef_seg(cnt11, n@pre, 100000) *
      IntArray::full(cnt20, n, c20) *
      IntArray::undef_seg(cnt20, n@pre, 100000) *
      IntArray::full(cnt21, n, c21) *
      IntArray::undef_seg(cnt21, n@pre, 100000)
   */
  for (int i = 0; i < n; ++i) {
    int a = seg1[i];
    int b = seg2[i];
    /*@ Assert exists sg1 sg2 c10 c11 c20 c21 rest prefix1 prefix2,
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre && n == n@pre &&
      1 <= n && n <= 100000 && 0 <= i && i <= n && 0 <= ans && ans <= i &&
      Forall(Z::le(0), s1_l) && Forall(Z::ge(1), s1_l) &&
      Forall(Z::le(0), s2_l) && Forall(Z::ge(1), s2_l) &&
      Forall(Z::le(0), t1_l) && Forall(Z::ge(1), t1_l) &&
      Forall(Z::le(0), t2_l) && Forall(Z::ge(1), t2_l) &&
      Forall(Z::le(0), c10) && Forall(Z::ge(n), c10) &&
      Forall(Z::le(0), c11) && Forall(Z::ge(n), c11) &&
      Forall(Z::le(0), c20) && Forall(Z::ge(n), c20) &&
      Forall(Z::le(0), c21) && Forall(Z::ge(n), c21) &&
      EditSegmentMeaning(t1_l, n, sg1) && EditSegmentMeaning(t2_l, n, sg2) &&
      Zlength(prefix1) == i && Zlength(prefix2) == i && ans == EditPairMatches(prefix1, prefix2) &&
      EditRemainingMatches(s1_l, s2_l, t1_l, t2_l, sg1, sg2, prefix1, prefix2, i, c10, c11, c20, c21, rest) &&
      EditStringsAnswer(map(Z::add(48), s1_l), map(Z::add(48), s2_l), map(Z::add(48), t1_l), map(Z::add(48), t2_l), ans + rest) &&
      IntArray::full(s1, n, s1_l) *
      IntArray::full(s2, n, s2_l) *
      IntArray::full(t1, n, t1_l) *
      IntArray::full(t2, n, t2_l) *
      IntArray::full(seg1, n, sg1) *
      IntArray::undef_seg(seg1, n@pre, 100000) * IntArray::full(seg2, n, sg2) *
      IntArray::undef_seg(seg2, n@pre, 100000) *
      IntArray::full(cnt10, n, c10) *
      IntArray::undef_seg(cnt10, n@pre, 100000) *
      IntArray::full(cnt11, n, c11) *
      IntArray::undef_seg(cnt11, n@pre, 100000) *
      IntArray::full(cnt20, n, c20) *
      IntArray::undef_seg(cnt20, n@pre, 100000) *
      IntArray::full(cnt21, n, c21) *
      IntArray::undef_seg(cnt21, n@pre, 100000) &&
      i < n && a == Znth(i, sg1, 0) && b == Znth(i, sg2, 0) &&
      0 <= a && a < n && 0 <= b && b < n
     */
    if (cnt10[a] > 0 && cnt20[b] > 0) {
      ans++; cnt10[a]--; cnt20[b]--;
    } else if (cnt11[a] > 0 && cnt21[b] > 0) {
      ans++; cnt11[a]--; cnt21[b]--;
    } else if (cnt10[a] > 0) {
      cnt10[a]--; cnt21[b]--;
    } else {
      cnt11[a]--; cnt20[b]--;
    }
  }
    /*@ Assert
      s1 == s1@pre && s2 == s2@pre && t1 == t1@pre && t2 == t2@pre && n == n@pre &&
EditStringsAnswer(map(Z::add(48), s1_l), map(Z::add(48), s2_l), map(Z::add(48), t1_l), map(Z::add(48), t2_l), ans) &&
      IntArray::full(s1, n, s1_l) *
      IntArray::full(s2, n, s2_l) *
      IntArray::full(t1, n, t1_l) *
      IntArray::full(t2, n, t2_l) *
      IntArray::undef_full(seg1, 100000) *
      IntArray::undef_full(seg2, 100000) *
      IntArray::undef_full(cnt10, 100000) *
      IntArray::undef_full(cnt11, 100000) *
      IntArray::undef_full(cnt20, 100000) *
      IntArray::undef_full(cnt21, 100000)
     */
  return ans;
}
