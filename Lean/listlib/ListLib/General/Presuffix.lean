import ListLib.General.Length
import Std.Tactic

namespace ListLib

universe u

def is_prefix {A : Type u} (l1 l2 : List A) : Prop :=
  exists l3, l2 = l1 ++ l3

def is_suffix {A : Type u} (l1 l2 : List A) : Prop :=
  exists l3, l2 = l3 ++ l1

def is_sublist {A : Type u} (l1 l2 : List A) : Prop :=
  exists l3 l4, l2 = l3 ++ l1 ++ l4

infix:70 " is_a_prefix_of " => is_prefix
infix:70 " is_a_suffix_of " => is_suffix
infix:70 " is_a_sublist_of " => is_sublist

def presuffix {A : Type u} (l1 l2 : List A) : Prop :=
  l1 is_a_prefix_of l2 /\ l1 is_a_suffix_of l2

def partial_match_res {A : Type u} (patn text res : List A) : Prop :=
  res is_a_suffix_of text /\ res is_a_prefix_of patn

def partial_bound_res {A : Type u} (patn text bound : List A) : Prop :=
  forall res, partial_match_res patn text res -> res.length <= bound.length

def proper_presuffix {A : Type u} (l1 l2 : List A) : Prop :=
  presuffix l1 l2 /\ l1.length < l2.length

def presuffix_bound {A : Type u} (l1 l2 : List A) : Prop :=
  forall l3, proper_presuffix l3 l2 -> presuffix l3 l1

def max_proper_presuffix {A : Type u} (l1 l2 : List A) : Prop :=
  proper_presuffix l1 l2 /\ presuffix_bound l1 l2

private theorem is_prefix_iff_builtin {A : Type u} {l1 l2 : List A} :
    is_prefix l1 l2 <-> l1 <+: l2 := by
  constructor
  · rintro ⟨l3, h⟩
    exact ⟨l3, h.symm⟩
  · rintro ⟨l3, h⟩
    exact ⟨l3, h.symm⟩

private theorem is_suffix_iff_builtin {A : Type u} {l1 l2 : List A} :
    is_suffix l1 l2 <-> l1 <:+ l2 := by
  constructor
  · rintro ⟨l3, h⟩
    exact ⟨l3, h.symm⟩
  · rintro ⟨l3, h⟩
    exact ⟨l3, h.symm⟩

private theorem is_sublist_iff_builtin {A : Type u} {l1 l2 : List A} :
    is_sublist l1 l2 <-> l1 <:+: l2 := by
  constructor
  · rintro ⟨l3, l4, h⟩
    exact ⟨l3, l4, h.symm⟩
  · rintro ⟨l3, l4, h⟩
    exact ⟨l3, l4, h.symm⟩

private theorem nth_eq_getElem {A : Type u} (d : A) (l : List A)
    (i : Nat) (h : i < l.length) :
    nth i l d = l[i] := by
  unfold nth AUXLib.nth
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

private theorem nth_append_left {A : Type u} (d : A) (l1 l2 : List A)
    (i : Nat) (h : i < l1.length) :
    nth i (l1 ++ l2) d = nth i l1 d := by
  have hcat : i < (l1 ++ l2).length := by
    simp
    omega
  exact (nth_eq_getElem d (l1 ++ l2) i hcat).trans
    ((List.getElem_append_left h).trans (nth_eq_getElem d l1 i h).symm)

private theorem nth_append_right {A : Type u} (d : A) (l1 l2 : List A)
    (i : Nat) (hlo : l1.length <= i) (hhi : i < (l1 ++ l2).length) :
    nth i (l1 ++ l2) d = nth (i - l1.length) l2 d := by
  have hr : i - l1.length < l2.length := by
    simp at hhi
    omega
  exact (nth_eq_getElem d (l1 ++ l2) i hhi).trans
    ((List.getElem_append_right hlo).trans
      (nth_eq_getElem d l2 (i - l1.length) hr).symm)

private theorem nth_append_single_last {A : Type u} (d : A) (l : List A)
    (a : A) :
    nth l.length (l ++ [a]) d = a := by
  simp [nth, AUXLib.nth]

theorem prefix_ind_iff_positional {A : Type u} (l1 l2 : List A) :
    l1 is_a_prefix_of l2 <-> exists hi, l1 = firstn hi l2 := by
  constructor
  · rintro ⟨l3, rfl⟩
    exact ⟨l1.length, by simp [firstn, AUXLib.firstn]⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨skipn hi l2, by
      simp [firstn, skipn, AUXLib.firstn, AUXLib.skipn, List.take_append_drop]⟩

theorem suffix_ind_iff_positional {A : Type u} (l1 l2 : List A) :
    l1 is_a_suffix_of l2 <-> exists lo, l1 = skipn lo l2 := by
  constructor
  · rintro ⟨l3, rfl⟩
    exact ⟨l3.length, by simp [skipn, AUXLib.skipn]⟩
  · rintro ⟨lo, rfl⟩
    exact ⟨firstn lo l2, by
      simp [firstn, skipn, AUXLib.firstn, AUXLib.skipn, List.take_append_drop]⟩

theorem sublist_ind_iff_positional {A : Type u} (l1 l2 : List A) :
    l1 is_a_sublist_of l2 <->
      exists lo hi, l1 = skipn lo (firstn hi l2) := by
  constructor
  · rintro ⟨p, q, rfl⟩
    refine ⟨p.length, p.length + l1.length, ?_⟩
    have hsub :
        Nsublist p.length (p.length + l1.length) (p ++ (l1 ++ q)) = l1 := by
      rw [@Nsublist_split_app_r A p.length (p.length + l1.length)
          p.length p (l1 ++ q) rfl ⟨Nat.le_refl _, by omega⟩]
      have h := @Nsublist_split_app_l A 0 l1.length l1 q (by omega)
        (Nat.le_refl _)
      change Nsublist 0 l1.length (l1 ++ q) =
        Nsublist 0 l1.length l1 at h
      simp only [Nat.sub_self, Nat.add_sub_cancel_left]
      rw [h, Nsublist_self l1 l1.length rfl]
    simpa [Nsublist, AUXLib.Nsublist, firstn, skipn, AUXLib.firstn,
      AUXLib.skipn, List.append_assoc] using hsub.symm
  · rintro ⟨lo, hi, rfl⟩
    exact ⟨firstn lo (firstn hi l2), skipn hi l2, by
      simp [firstn, skipn, AUXLib.firstn, AUXLib.skipn, List.take_append_drop]⟩

theorem prefix_snoc {A : Type u} (l0 l : List A) (a : A) :
    l0 is_a_prefix_of (l ++ [a]) <-> l0 is_a_prefix_of l \/ l ++ [a] = l0 := by
  rw [is_prefix_iff_builtin, is_prefix_iff_builtin, List.prefix_concat_iff]
  constructor
  · rintro (h | h)
    · exact Or.inr h.symm
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h.symm

theorem sublist_snor {A : Type u} (l0 l : List A) (a : A) :
    l0 is_a_sublist_of (l ++ [a]) <->
      l0 is_a_sublist_of l \/ l0 is_a_suffix_of (l ++ [a]) := by
  rw [is_sublist_iff_builtin, is_sublist_iff_builtin, is_suffix_iff_builtin,
    List.infix_concat_iff]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h

theorem prefix_of_nil_inv {A : Type u} (l : List A) :
    l is_a_prefix_of [] -> l = [] := by
  rintro ⟨l', h⟩
  have hlen : 0 = l.length + l'.length := by
    simpa only [List.length_nil, List.length_append] using congrArg List.length h
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem sublist_of_nil_inv {A : Type u} (l : List A) :
    l is_a_sublist_of [] -> l = [] := by
  rintro ⟨l', l'', h⟩
  have hlen := congrArg List.length h
  simp only [List.length_nil, List.length_append] at hlen
  have hzero : l.length = 0 := by omega
  exact List.eq_nil_of_length_eq_zero hzero

theorem is_suffix_snoc_snoc_iff {A : Type u} (l1 l2 : List A) (a1 a2 : A) :
    (l1 ++ [a1]) is_a_suffix_of (l2 ++ [a2]) <->
      l1 is_a_suffix_of l2 /\ a1 = a2 := by
  constructor
  · rintro ⟨l, h⟩
    rw [(List.append_assoc l l1 [a1]).symm] at h
    have hs := List.append_inj' h (by simp)
    exact ⟨⟨l, hs.1⟩, (List.cons.inj hs.2).1.symm⟩
  · rintro ⟨⟨l, rfl⟩, rfl⟩
    exact ⟨l, by simp [List.append_assoc]⟩

theorem prefix_length {A : Type u} (l1 l2 : List A) :
    l1 is_a_prefix_of l2 -> l1.length <= l2.length := by
  rintro ⟨l3, rfl⟩
  simp

theorem suffix_length {A : Type u} (l1 l2 : List A) :
    l1 is_a_suffix_of l2 -> l1.length <= l2.length := by
  rintro ⟨l3, rfl⟩
  simp

theorem presuffix_length {A : Type u} (l1 l2 : List A) :
    presuffix l1 l2 -> l1.length <= l2.length := by
  intro h
  exact prefix_length l1 l2 h.1

theorem prefix_iff {A : Type u} (default : A) (l1 l2 : List A) :
    l1 is_a_prefix_of l2 <->
      (l1.length <= l2.length /\
        forall i, 0 <= i /\ i < l1.length ->
          nth i l1 default = nth i l2 default) := by
  constructor
  · intro h
    have hb := is_prefix_iff_builtin.mp h
    have hlen := prefix_length l1 l2 h
    refine ⟨hlen, ?_⟩
    intro i hi
    have h2 : i < l2.length := Nat.lt_of_lt_of_le hi.2 hlen
    exact (nth_eq_getElem default l1 i hi.2).trans
      ((hb.getElem hi.2).trans (nth_eq_getElem default l2 i h2).symm)
  · rintro ⟨hlen, hnth⟩
    apply is_prefix_iff_builtin.mpr
    apply List.prefix_iff_getElem.mpr
    refine ⟨hlen, ?_⟩
    intro i hi
    have hi2 : i < l2.length := Nat.lt_of_lt_of_le hi hlen
    have h := hnth i ⟨Nat.zero_le i, hi⟩
    rw [nth_eq_getElem default l1 i hi, nth_eq_getElem default l2 i hi2] at h
    exact h

theorem prefix_iff' {A : Type u} (l1 l2 : List A) :
    l1 is_a_prefix_of l2 <->
      (l1.length <= l2.length /\
        forall default i, 0 <= i /\ i < l1.length ->
          nth i l1 default = nth i l2 default) := by
  constructor
  · intro h
    refine ⟨prefix_length l1 l2 h, ?_⟩
    intro default
    exact (prefix_iff default l1 l2).mp h |>.2
  · rintro ⟨hlen, hnth⟩
    cases l1 with
    | nil => exact ⟨l2, rfl⟩
    | cons a l =>
        exact (prefix_iff a (a :: l) l2).mpr ⟨hlen, hnth a⟩

theorem suffix_iff {A : Type u} (default : A) (l1 l2 : List A) :
    l1 is_a_suffix_of l2 <->
      (l1.length <= l2.length /\
        forall i, 0 <= i /\ i < l1.length ->
          nth (l1.length - 1 - i) l1 default =
          nth (l2.length - 1 - i) l2 default) := by
  constructor
  · intro h
    have hb := is_suffix_iff_builtin.mp h
    have hlen := suffix_length l1 l2 h
    refine ⟨hlen, ?_⟩
    intro i hi
    let j := l1.length - 1 - i
    have hj : j < l1.length := by
      dsimp [j]
      omega
    have hj2 : l2.length - l1.length + j = l2.length - 1 - i := by
      dsimp [j]
      omega
    have hs := hb.getElem hj
    have hs' : l1[j] = l2[l2.length - 1 - i] := by
      simpa only [hj2] using hs
    have h2 : l2.length - 1 - i < l2.length := by omega
    exact (nth_eq_getElem default l1 j hj).trans
      (hs'.trans (nth_eq_getElem default l2 (l2.length - 1 - i) h2).symm)
  · rintro ⟨hlen, hnth⟩
    apply is_suffix_iff_builtin.mpr
    apply List.suffix_iff_getElem.mpr
    refine ⟨hlen, ?_⟩
    intro i hi
    let j := l1.length - 1 - i
    have hj : j < l1.length := by
      dsimp [j]
      omega
    have hidx : i + l2.length - l1.length < l2.length := by omega
    have hidxEq : l2.length - 1 - j = i + l2.length - l1.length := by
      dsimp [j]
      omega
    have hleftEq : l1.length - 1 - j = i := by
      dsimp [j]
      omega
    have h := hnth j ⟨Nat.zero_le j, hj⟩
    rw [hleftEq, hidxEq, nth_eq_getElem default l1 i hi,
      nth_eq_getElem default l2 (i + l2.length - l1.length) hidx] at h
    exact h.symm

theorem suffix_iff' {A : Type u} (l1 l2 : List A) :
    l1 is_a_suffix_of l2 <->
      (l1.length <= l2.length /\
        forall default i, 0 <= i /\ i < l1.length ->
          nth (l1.length - 1 - i) l1 default =
          nth (l2.length - 1 - i) l2 default) := by
  constructor
  · intro h
    refine ⟨suffix_length l1 l2 h, ?_⟩
    intro default
    exact (suffix_iff default l1 l2).mp h |>.2
  · rintro ⟨hlen, hnth⟩
    cases l1 with
    | nil => exact ⟨l2, by simp⟩
    | cons a l =>
        exact (suffix_iff a (a :: l) l2).mpr ⟨hlen, hnth a⟩

theorem is_prefix_snoc_iff {A : Type u} (default : A)
    (l1 l2 : List A) (a : A) :
    (l1 ++ [a]) is_a_prefix_of l2 <->
      (l1.length < l2.length /\
        l1 is_a_prefix_of l2 /\
        a = nth l1.length l2 default) := by
  constructor
  · intro h
    have hb := is_prefix_iff_builtin.mp h
    have hlen := prefix_length (l1 ++ [a]) l2 h
    refine ⟨by simpa using hlen, ?_, ?_⟩
    · rcases h with ⟨tail, rfl⟩
      exact ⟨[a] ++ tail, by simp [List.append_assoc]⟩
    · have hlast : l1.length < (l1 ++ [a]).length := by simp
      have h2 : l1.length < l2.length :=
        Nat.lt_of_lt_of_le hlast hlen
      have hp := hb.getElem hlast
      have hleft := nth_append_single_last default l1 a
      have helemLeft : (l1 ++ [a])[l1.length] = a :=
        (nth_eq_getElem default (l1 ++ [a]) l1.length hlast).symm.trans hleft
      have hright := nth_eq_getElem default l2 l1.length h2
      exact helemLeft.symm.trans (hp.trans hright.symm)
  · rintro ⟨hlt, hp, ha⟩
    rw [prefix_iff default] at hp ⊢
    refine ⟨by simpa [List.length_append] using Nat.succ_le_of_lt hlt, ?_⟩
    intro i hi
    have hlen1 : (l1 ++ [a]).length = l1.length + 1 := by simp
    by_cases hlt1 : i < l1.length
    · have hleft := nth_eq_getElem default (l1 ++ [a]) i (by omega)
      have hprefix := hp.2 i ⟨Nat.zero_le i, hlt1⟩
      have happ : nth i (l1 ++ [a]) default = nth i l1 default := by
        exact nth_append_left default l1 [a] i hlt1
      exact happ.trans hprefix
    · have hiEq : i = l1.length := by omega
      subst i
      have hleft := nth_append_single_last default l1 a
      exact hleft.trans ha

theorem prefix_trans {A : Type u} (l1 l2 l3 : List A) :
    l1 is_a_prefix_of l2 ->
    l2 is_a_prefix_of l3 ->
    l1 is_a_prefix_of l3 := by
  rintro ⟨r1, rfl⟩ ⟨r2, rfl⟩
  exact ⟨r1 ++ r2, by simp [List.append_assoc]⟩

theorem suffix_trans {A : Type u} (l1 l2 l3 : List A) :
    l1 is_a_suffix_of l2 ->
    l2 is_a_suffix_of l3 ->
    l1 is_a_suffix_of l3 := by
  rintro ⟨r1, rfl⟩ ⟨r2, rfl⟩
  exact ⟨r2 ++ r1, by simp [List.append_assoc]⟩

theorem presuffix_trans {A : Type u} (l1 l2 l3 : List A) :
    presuffix l1 l2 ->
    presuffix l2 l3 ->
    presuffix l1 l3 := by
  rintro ⟨hp12, hs12⟩ ⟨hp23, hs23⟩
  exact ⟨prefix_trans l1 l2 l3 hp12 hp23,
    suffix_trans l1 l2 l3 hs12 hs23⟩

theorem prefix_total_order {A : Type u} (l1 l2 l : List A) :
    l1 is_a_prefix_of l ->
    l2 is_a_prefix_of l ->
    l1.length <= l2.length ->
    l1 is_a_prefix_of l2 := by
  intro h1 h2 hlen
  exact is_prefix_iff_builtin.mpr
    (List.prefix_of_prefix_length_le
      (is_prefix_iff_builtin.mp h1) (is_prefix_iff_builtin.mp h2) hlen)

theorem suffix_total_order {A : Type u} (l1 l2 l : List A) :
    l1 is_a_suffix_of l ->
    l2 is_a_suffix_of l ->
    l1.length <= l2.length ->
    l1 is_a_suffix_of l2 := by
  intro h1 h2 hlen
  exact is_suffix_iff_builtin.mpr
    (List.suffix_of_suffix_length_le
      (is_suffix_iff_builtin.mp h1) (is_suffix_iff_builtin.mp h2) hlen)

theorem partial_match_total_order {A : Type u}
    (l1 l2 patn text : List A) :
    partial_match_res patn text l1 ->
    partial_match_res patn text l2 ->
    l1.length <= l2.length ->
    presuffix l1 l2 := by
  rintro ⟨hs1, hp1⟩ ⟨hs2, hp2⟩ hlen
  exact ⟨prefix_total_order l1 l2 patn hp1 hp2 hlen,
    suffix_total_order l1 l2 text hs1 hs2 hlen⟩

theorem partial_match_iff {A : Type u} (res0 patn text : List A) :
    partial_match_res patn text res0 ->
    partial_bound_res patn text res0 ->
    forall res,
      partial_match_res patn text res <-> presuffix res res0 := by
  intro hres0 hbound res
  constructor
  · intro hres
    exact partial_match_total_order res res0 patn text hres hres0
      (hbound res hres)
  · rintro ⟨hp, hs⟩
    exact ⟨suffix_trans res res0 text hs hres0.1,
      prefix_trans res res0 patn hp hres0.2⟩

theorem partial_match_snoc_iff {A : Type u} (default : A)
    (res patn text : List A) (ch : A) :
    partial_match_res patn (text ++ [ch]) res <->
      res = [] \/
      exists res',
        res = res' ++ [ch] /\
        res'.length < patn.length /\
        nth res'.length patn default = ch /\
        partial_match_res patn text res' := by
  constructor
  · intro h
    rcases list_snoc_destruct res with rfl | ⟨ch0, res', rfl⟩
    · exact Or.inl rfl
    · have hs := (is_suffix_snoc_snoc_iff res' text ch0 ch).mp h.1
      refine Or.inr ⟨res', ?_, ?_, ?_, ?_⟩
      · rw [hs.2]
      · have hplen := prefix_length (res' ++ [ch0]) patn h.2
        simpa using hplen
      · rcases h.2 with ⟨tail, rfl⟩
        rw [hs.2]
        simp [nth, AUXLib.nth, List.append_assoc]
      · exact ⟨hs.1, prefix_trans res' (res' ++ [ch0]) patn
          ⟨[ch0], rfl⟩ h.2⟩
  · rintro (rfl | ⟨res', rfl, hlen, hnth, hpartial⟩)
    · exact ⟨⟨text ++ [ch], by simp⟩, ⟨patn, rfl⟩⟩
    · exact ⟨(is_suffix_snoc_snoc_iff res' text ch ch).mpr
          ⟨hpartial.1, rfl⟩,
        (is_prefix_snoc_iff default res' patn ch).mpr
          ⟨hlen, hpartial.2, hnth.symm⟩⟩

theorem prefix_iff_sublist {A : Type u} (l1 l2 : List A) :
    l1 is_a_prefix_of l2 <->
      (exists j, j = l1.length /\ l1 = Nsublist 0 j l2) := by
  constructor
  · rintro ⟨tail, rfl⟩
    refine ⟨l1.length, rfl, ?_⟩
    symm
    have h := @Nsublist_split_app_l A 0 l1.length l1 tail (by omega)
      (Nat.le_refl _)
    change Nsublist 0 l1.length (l1 ++ tail) = Nsublist 0 l1.length l1 at h
    rw [h, Nsublist_self l1 l1.length rfl]
  · rintro ⟨j, hj, hsub⟩
    have hjle : j <= l2.length := by
      have hlen := congrArg List.length hsub
      rw [length_sublist'] at hlen
      omega
    refine ⟨Nsublist j l2.length l2, ?_⟩
    calc
      l2 = Nsublist 0 l2.length l2 := (Nsublist_self l2 l2.length rfl).symm
      _ = Nsublist 0 j l2 ++ Nsublist j l2.length l2 :=
        @Nsublist_split A 0 l2.length j l2
          ⟨Nat.zero_le _, Nat.zero_le _⟩ ⟨hjle, Nat.le_refl _⟩
      _ = l1 ++ Nsublist j l2.length l2 := by rw [← hsub]

theorem suffix_iff_sublist {A : Type u} (l1 l2 : List A) :
    l1 is_a_suffix_of l2 <->
      (exists i, i = l2.length - l1.length /\
        l1 = Nsublist i l2.length l2) := by
  constructor
  · rintro ⟨head, rfl⟩
    refine ⟨head.length, ?_, ?_⟩
    · simp
    · symm
      have h := @Nsublist_split_app_r A head.length (head.length + l1.length)
        head.length head l1 rfl ⟨Nat.le_refl _, by omega⟩
      simp only [Nat.sub_self, Nat.add_sub_cancel_left] at h
      simpa [List.length_append] using h.trans (Nsublist_self l1 l1.length rfl)
  · rintro ⟨i, hi, hsub⟩
    have hile : i <= l2.length := by omega
    refine ⟨Nsublist 0 i l2, ?_⟩
    calc
      l2 = Nsublist 0 l2.length l2 := (Nsublist_self l2 l2.length rfl).symm
      _ = Nsublist 0 i l2 ++ Nsublist i l2.length l2 :=
        @Nsublist_split A 0 l2.length i l2
          ⟨Nat.zero_le _, Nat.zero_le _⟩ ⟨hile, Nat.le_refl _⟩
      _ = Nsublist 0 i l2 ++ l1 := by rw [← hsub]

theorem nil_prefix {A : Type u} (l : List A) :
    [] is_a_prefix_of l := by
  exact ⟨l, rfl⟩

theorem nil_suffix {A : Type u} (l : List A) :
    [] is_a_suffix_of l := by
  exact ⟨l, by simp⟩

theorem nil_presuffix {A : Type u} (l : List A) :
    presuffix [] l := by
  exact ⟨nil_prefix l, nil_suffix l⟩

theorem presuffix_nil_iff {A : Type u} (l : List A) :
    presuffix l [] <-> l = [] := by
  constructor
  · intro h
    exact prefix_of_nil_inv l h.1
  · rintro rfl
    exact nil_presuffix []

theorem partial_match_nil {A : Type u} (patn text : List A) :
    partial_match_res patn text [] := by
  exact ⟨nil_suffix text, nil_prefix patn⟩

theorem presuffix_partial_match {A : Type u} (p t l0 l1 : List A) :
    partial_match_res p t l0 ->
    presuffix l1 l0 ->
    partial_match_res p t l1 := by
  rintro ⟨hs0, hp0⟩ ⟨hp1, hs1⟩
  exact ⟨suffix_trans l1 l0 t hs1 hs0,
    prefix_trans l1 l0 p hp1 hp0⟩

theorem prefix_app_iff {A : Type u} (l1 l2 l3 : List A) :
    l1 is_a_prefix_of l2 <->
      l1.length <= l2.length /\ l1 is_a_prefix_of (l2 ++ l3) := by
  constructor
  · intro h
    refine ⟨prefix_length l1 l2 h, ?_⟩
    rcases h with ⟨tail, rfl⟩
    exact ⟨tail ++ l3, by simp [List.append_assoc]⟩
  · rintro ⟨hlen, hprefix⟩
    rw [prefix_iff'] at hprefix ⊢
    refine ⟨hlen, ?_⟩
    intro default i hi
    have hi2 : i < l2.length := Nat.lt_of_lt_of_le hi.2 hlen
    have h := hprefix.2 default i hi
    have happ : nth i (l2 ++ l3) default = nth i l2 default := by
      exact nth_append_left default l2 l3 i hi2
    exact h.trans happ

theorem suffix_app_iff {A : Type u} (l1 l2 l3 : List A) :
    l1 is_a_suffix_of l2 <->
      l1.length <= l2.length /\ l1 is_a_suffix_of (l3 ++ l2) := by
  constructor
  · intro h
    refine ⟨suffix_length l1 l2 h, ?_⟩
    rcases h with ⟨head, rfl⟩
    exact ⟨l3 ++ head, by simp [List.append_assoc]⟩
  · rintro ⟨hlen, hsuffix⟩
    rw [suffix_iff'] at hsuffix ⊢
    refine ⟨hlen, ?_⟩
    intro default i hi
    have hidx : l3.length <= (l3 ++ l2).length - 1 - i := by
      simp
      omega
    have h := hsuffix.2 default i hi
    have happ : nth ((l3 ++ l2).length - 1 - i) (l3 ++ l2) default =
        nth (l2.length - 1 - i) l2 default := by
      have hhi : (l3 ++ l2).length - 1 - i < (l3 ++ l2).length := by omega
      have h := nth_append_right default l3 l2 ((l3 ++ l2).length - 1 - i)
        hidx hhi
      have heq : (l3 ++ l2).length - 1 - i - l3.length =
          l2.length - 1 - i := by
        simp
        omega
      simpa only [heq] using h
    exact h.trans happ

theorem prefix_sublist_iff {A : Type u} (l0 l : List A) (i : Nat)
    (hi : 0 <= i /\ i <= l.length) :
    l0 is_a_prefix_of (Nsublist 0 i l) <->
      l0.length <= i /\ l0 is_a_prefix_of l := by
  have hlen : (Nsublist 0 i l).length = i := by
    exact length_sublist 0 i l ⟨Nat.zero_le _, hi.2⟩
  have hpSub : (Nsublist 0 i l) is_a_prefix_of l := by
    refine ⟨Nsublist i l.length l, ?_⟩
    rw [← @Nsublist_split A 0 l.length i l
      ⟨Nat.zero_le _, Nat.zero_le _⟩ ⟨hi.2, Nat.le_refl _⟩]
    exact (Nsublist_self l l.length rfl).symm
  constructor
  · intro h
    exact ⟨by have := prefix_length l0 (Nsublist 0 i l) h; omega,
      prefix_trans l0 (Nsublist 0 i l) l h hpSub⟩
  · rintro ⟨hlen0, hp⟩
    exact prefix_total_order l0 (Nsublist 0 i l) l hp hpSub (by omega)

theorem suffix_sublist_cons_iff {A : Type u} (l0 l : List A) (i : Nat)
    (hi : 1 <= i /\ i <= l.length) :
    l0 is_a_suffix_of (Nsublist 1 i l) <->
      l0.length <= i - 1 /\ l0 is_a_suffix_of (Nsublist 0 i l) := by
  have hlen : (Nsublist 1 i l).length = i - 1 := by
    exact length_sublist 1 i l hi
  have hsSub : (Nsublist 1 i l) is_a_suffix_of (Nsublist 0 i l) := by
    refine ⟨Nsublist 0 1 l, ?_⟩
    exact @Nsublist_split A 0 i 1 l
      ⟨Nat.zero_le _, by omega⟩ ⟨hi.1, hi.2⟩
  constructor
  · intro h
    exact ⟨by have := suffix_length l0 (Nsublist 1 i l) h; omega,
      suffix_trans l0 (Nsublist 1 i l) (Nsublist 0 i l) h hsSub⟩
  · rintro ⟨hlen0, hs⟩
    exact suffix_total_order l0 (Nsublist 1 i l) (Nsublist 0 i l)
      hs hsSub (by omega)

end ListLib
