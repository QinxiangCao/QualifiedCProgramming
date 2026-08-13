import MonadLib.UnifiedTactics
import ListLib.Base.Positional
import ListLib.Base.Inductive
import ListLib.General.Length

namespace MonadLib.Examples.kmp

open AUXLib
open MonadLib
open scoped MonadNotation

def inner_body {A : Type} (default : A) (str : List A) (vnext : List Int)
    (ch : A) : Int -> program Unit (CntOrBrk Int Int) :=
  fun j =>
    MonadLib.assert (0 <= j /\ j < Zlength str) ;;
    MonadLib.assert (j < Zlength vnext) ;;
    choice
      (testPure (ch = Znth j str default) ;; MonadLib.break (j + 1))
      (testPure (Not (ch = Znth j str default)) ;;
        choice
          (testPure (j = 0) ;; MonadLib.break 0)
          (testPure (Not (j = 0)) ;; MonadLib.continue (Znth (j - 1) vnext 0)))

def inner_loop {A : Type} (default : A) (str : List A) (vnext : List Int)
    (ch : A) : Int -> program Unit Int :=
  repeat_break (inner_body default str vnext ch)

def constr_body {A : Type} (default : A) (str : List A) :
    Int -> Prod (List Int) Int -> program Unit (Prod (List Int) Int) :=
  fun i (vnext, j) =>
    MonadLib.assert (i < Zlength str) ;;
    let ch := Znth i str default
    j' <- inner_loop default str vnext ch j ;;
    MonadErr.ret (vnext ++ [j'], j')

def constr_loop {A : Type} (default : A) (str : List A) :
    program Unit (List Int) :=
  (vnext, _) <- range_iter 1 (Zlength str) (constr_body default str) ([0], 0) ;;
  MonadErr.ret vnext

def match_body {A : Type} (default : A) (patn text : List A) (vnext : List Int) :
    Int -> Int -> program Unit (CntOrBrk Int Int) :=
  fun i j =>
    MonadLib.assert (i < Zlength text) ;;
    let ch := Znth i text default
    j' <- inner_loop default patn vnext ch j ;;
    choice
      (testPure (j' = Zlength patn) ;; MonadLib.break (i - Zlength patn + 1))
      (testPure (j' < Zlength patn) ;; MonadLib.continue j')

def match_loop {A : Type} (default : A) (patn text : List A) (vnext : List Int) :
    program Unit (Option Int) :=
  res <- range_iter_break 0 (Zlength text) (match_body default patn text vnext) 0 ;;
  match res with
  | .by_continue _ => MonadErr.ret none
  | .by_break i => MonadErr.ret (some i)

def is_prefix {A : Type} (l1 l2 : List A) : Prop :=
  exists l, l2 = l1 ++ l

def is_suffix {A : Type} (l1 l2 : List A) : Prop :=
  exists l, l2 = l ++ l1

def presuffix {A : Type} (l1 l2 : List A) : Prop :=
  is_prefix l1 l2 /\ is_suffix l1 l2

def partial_match_result {A : Type} (patn text res : List A) : Prop :=
  is_suffix res text /\ is_prefix res patn

def best_partial_match_result {A : Type} (patn text res : List A) : Prop :=
  partial_match_result patn text res /\
    forall res', partial_match_result patn text res' -> Zlength res' <= Zlength res

def proper_presuffix {A : Type} (l1 l2 : List A) : Prop :=
  presuffix l1 l2 /\ Zlength l1 < Zlength l2

def max_proper_presuffix {A : Type} (l1 l2 : List A) : Prop :=
  proper_presuffix l1 l2 /\
    forall l3, proper_presuffix l3 l2 -> presuffix l3 l1

def is_prefix_func {A : Type} (vnext : List Int) (patn : List A) : Prop :=
  forall i0 : Int, 0 <= i0 /\ i0 < Zlength vnext ->
    0 <= Znth i0 vnext 0 /\ Znth i0 vnext 0 <= i0 /\
    max_proper_presuffix
      (sublist 0 (Znth i0 vnext 0) patn)
      (sublist 0 (i0 + 1) patn)

theorem is_suffix_snoc_snoc_iff {A : Type} (l1 l2 : List A) (a1 a2 : A) :
    is_suffix (l1 ++ [a1]) (l2 ++ [a2]) <->
      is_suffix l1 l2 /\ a1 = a2 := by
  constructor
  · rintro ⟨l, h⟩
    rw [(List.append_assoc l l1 [a1]).symm] at h
    have hs := List.append_inj' h (by simp)
    exact ⟨⟨l, hs.1⟩, (List.cons.inj hs.2).1.symm⟩
  · rintro ⟨⟨l, rfl⟩, rfl⟩
    exact ⟨l, by simp [List.append_assoc]⟩

theorem prefix_Zlength {A : Type} (l1 l2 : List A) :
    is_prefix l1 l2 -> Zlength l1 <= Zlength l2 := by
  rintro ⟨l, rfl⟩
  simp [ListLib.Zlength, AUXLib.Zlength]
  omega

theorem suffix_Zlength {A : Type} (l1 l2 : List A) :
    is_suffix l1 l2 -> Zlength l1 <= Zlength l2 := by
  rintro ⟨l, rfl⟩
  simp [ListLib.Zlength, AUXLib.Zlength]
  omega

theorem presuffix_Zlength {A : Type} (l1 l2 : List A) :
    presuffix l1 l2 -> Zlength l1 <= Zlength l2 := by
  exact fun h => prefix_Zlength l1 l2 h.1

theorem prefix_iff {A : Type} (default : A) (l1 l2 : List A) :
    is_prefix l1 l2 <->
      (Zlength l1 <= Zlength l2 /\
        forall i, 0 <= i /\ i < Zlength l1 ->
          Znth i l1 default = Znth i l2 default) := by
  change is_prefix l1 l2 <->
    (AUXLib.Zlength l1 <= AUXLib.Zlength l2 /\
      forall i, 0 <= i /\ i < AUXLib.Zlength l1 ->
        AUXLib.Znth i l1 default = AUXLib.Znth i l2 default)
  constructor
  · rintro ⟨tail, rfl⟩
    constructor
    · exact prefix_Zlength l1 (l1 ++ tail) ⟨tail, rfl⟩
    · intro i hi
      exact (ListLib.app_Znth1 default l1 tail i hi).symm
  · rintro ⟨hlen, hnth⟩
    let tail := AUXLib.sublist (AUXLib.Zlength l1) (AUXLib.Zlength l2) l2
    refine ⟨tail, ?_⟩
    apply ListLib.list_eq_ext l2 (l1 ++ tail) default
    constructor
    · change AUXLib.Zlength l2 = AUXLib.Zlength (l1 ++ tail)
      have htail : AUXLib.Zlength tail = AUXLib.Zlength l2 - AUXLib.Zlength l1 := by
        exact ListLib.Zlength_sublist (AUXLib.Zlength l1) (AUXLib.Zlength l2) l2
          ⟨AUXLib.Zlength_nonneg l1, hlen⟩ (Int.le_refl _)
      have happ := AUXLib.Zlength_app l1 tail
      change AUXLib.Zlength (l1 ++ tail) =
        AUXLib.Zlength l1 + AUXLib.Zlength tail at happ
      omega
    · intro i hi
      change 0 <= i /\ i < AUXLib.Zlength l2 at hi
      by_cases hil : i < AUXLib.Zlength l1
      · exact (hnth i ⟨hi.1, hil⟩).symm.trans
          (ListLib.app_Znth1 default l1 tail i ⟨hi.1, hil⟩).symm
      · have happ := ListLib.app_Znth2 default l1 tail i (by omega)
        have hsub := ListLib.Znth_sublist default (AUXLib.Zlength l1)
          (i - AUXLib.Zlength l1) (AUXLib.Zlength l2) l2
          (AUXLib.Zlength_nonneg l1) (by omega)
        have heq : AUXLib.Znth (i - AUXLib.Zlength l1 + AUXLib.Zlength l1) l2 default =
            AUXLib.Znth i l2 default := by congr 1 <;> omega
        exact (happ.trans (hsub.trans heq)).symm

theorem prefix_iff' {A : Type} (l1 l2 : List A) :
    is_prefix l1 l2 <->
      (Zlength l1 <= Zlength l2 /\
        forall default i, 0 <= i /\ i < Zlength l1 ->
          Znth i l1 default = Znth i l2 default) := by
  constructor
  · intro h
    refine ⟨prefix_Zlength l1 l2 h, ?_⟩
    intro default
    exact (prefix_iff default l1 l2).mp h |>.2
  · rintro ⟨hlen, hnth⟩
    cases l1 with
    | nil => exact ⟨l2, rfl⟩
    | cons a l =>
        exact (prefix_iff a (a :: l) l2).mpr ⟨hlen, hnth a⟩

theorem suffix_iff {A : Type} (default : A) (l1 l2 : List A) :
    is_suffix l1 l2 <->
      (Zlength l1 <= Zlength l2 /\
        forall i, 0 <= i /\ i < Zlength l1 ->
          Znth (Zlength l1 - 1 - i) l1 default =
          Znth (Zlength l2 - 1 - i) l2 default) := by
  constructor
  · rintro ⟨head, rfl⟩
    constructor
    · exact suffix_Zlength l1 (head ++ l1) ⟨head, rfl⟩
    · intro i hi
      have hlen := AUXLib.Zlength_app head l1
      have hindex : AUXLib.Zlength (head ++ l1) - 1 - i >=
          AUXLib.Zlength head := by omega
      have happ := ListLib.app_Znth2 default head l1
        (AUXLib.Zlength (head ++ l1) - 1 - i) hindex
      have heq : AUXLib.Zlength (head ++ l1) - 1 - i - AUXLib.Zlength head =
          AUXLib.Zlength l1 - 1 - i := by omega
      simpa only [heq] using happ.symm
  · rintro ⟨hlen, hnth⟩
    change AUXLib.Zlength l1 <= AUXLib.Zlength l2 at hlen
    let head := AUXLib.sublist 0 (AUXLib.Zlength l2 - AUXLib.Zlength l1) l2
    have hlen1 := AUXLib.Zlength_nonneg l1
    have hlen2 := AUXLib.Zlength_nonneg l2
    have hheadLen : AUXLib.Zlength head =
        AUXLib.Zlength l2 - AUXLib.Zlength l1 := by
      have h := ListLib.Zlength_sublist 0
        (AUXLib.Zlength l2 - AUXLib.Zlength l1) l2
        (by constructor <;> omega) (by
          change AUXLib.Zlength l2 - AUXLib.Zlength l1 <= AUXLib.Zlength l2
          omega)
      change AUXLib.Zlength head =
        (AUXLib.Zlength l2 - AUXLib.Zlength l1) - 0 at h
      omega
    have htotal : AUXLib.Zlength l2 =
        AUXLib.Zlength head + AUXLib.Zlength l1 := by
      omega
    refine ⟨head, ?_⟩
    apply ListLib.list_eq_ext l2 (head ++ l1) default
    constructor
    · change AUXLib.Zlength l2 = AUXLib.Zlength (head ++ l1)
      have happ := AUXLib.Zlength_app head l1
      omega
    · intro i hi
      change 0 <= i /\ i < AUXLib.Zlength l2 at hi
      by_cases hip : i < AUXLib.Zlength l2 - AUXLib.Zlength l1
      · have happ := ListLib.app_Znth1 default head l1 i (by
            change 0 <= i /\ i < AUXLib.Zlength head
            omega)
        have hsub := ListLib.Znth_sublist default 0 i
          (AUXLib.Zlength l2 - AUXLib.Zlength l1) l2 (by omega) (by
            constructor <;> omega)
        simpa only [Int.add_zero] using (hsub.symm.trans happ.symm)
      ·
        have happ := ListLib.app_Znth2 default head l1 i (by omega)
        let j := AUXLib.Zlength l2 - 1 - i
        have hip' : Not (i < AUXLib.Zlength head) := by
          rw [hheadLen]
          exact hip
        have hi' : i < AUXLib.Zlength head + AUXLib.Zlength l1 := by
          rw [← htotal]
          exact hi.2
        have hjEq : j = AUXLib.Zlength head + AUXLib.Zlength l1 - 1 - i := by
          dsimp [j]
          simpa [ListLib.Zlength, AUXLib.Zlength] using
            congrArg (fun n : Int => n - 1 - i) htotal
        have hj : 0 <= j /\ j < AUXLib.Zlength l1 := by
          rw [hjEq]
          omega
        have hs := hnth j hj
        have heq1 : AUXLib.Zlength l1 - 1 - j =
            i - AUXLib.Zlength head := by
          rw [hjEq]
          omega
        have heq2 : AUXLib.Zlength l2 - 1 - j = i := by
          dsimp [j]
          omega
        rw [heq1, heq2] at hs
        exact hs.symm.trans happ.symm

theorem suffix_iff' {A : Type} (l1 l2 : List A) :
    is_suffix l1 l2 <->
      (Zlength l1 <= Zlength l2 /\
        forall default i, 0 <= i /\ i < Zlength l1 ->
          Znth (Zlength l1 - 1 - i) l1 default =
          Znth (Zlength l2 - 1 - i) l2 default) := by
  constructor
  · intro h
    refine ⟨suffix_Zlength l1 l2 h, ?_⟩
    intro default
    exact (suffix_iff default l1 l2).mp h |>.2
  · rintro ⟨hlen, hnth⟩
    cases l1 with
    | nil => exact ⟨l2, by simp⟩
    | cons a l =>
        exact (suffix_iff a (a :: l) l2).mpr ⟨hlen, hnth a⟩

theorem is_prefix_snoc_iff {A : Type} (default : A) (l1 l2 : List A) (a : A) :
    is_prefix (l1 ++ [a]) l2 <->
      (Zlength l1 < Zlength l2 /\ is_prefix l1 l2 /\
        a = Znth (Zlength l1) l2 default) := by
  change is_prefix (l1 ++ [a]) l2 <->
    (AUXLib.Zlength l1 < AUXLib.Zlength l2 /\ is_prefix l1 l2 /\
      a = AUXLib.Znth (AUXLib.Zlength l1) l2 default)
  rw [prefix_iff default, prefix_iff default]
  constructor
  · rintro ⟨hlen, hnth⟩
    change AUXLib.Zlength (l1 ++ [a]) <= AUXLib.Zlength l2 at hlen
    change (forall i, 0 <= i /\ i < AUXLib.Zlength (l1 ++ [a]) ->
      AUXLib.Znth i (l1 ++ [a]) default = AUXLib.Znth i l2 default) at hnth
    have happ : Zlength (l1 ++ [a]) = Zlength l1 + 1 := by
      simpa [ListLib.Zlength, AUXLib.Zlength]
    have hnonneg := AUXLib.Zlength_nonneg l1
    refine ⟨by omega, ⟨?_, ?_⟩⟩
    · refine ⟨by omega, ?_⟩
      intro i hi
      exact (ListLib.app_Znth1 default l1 [a] i hi).symm.trans
        (hnth i (by omega))
    · have hlast := hnth (Zlength l1) (by omega)
      have happLast := ListLib.app_Znth2 default l1 [a] (Zlength l1)
        (by omega)
      have hvalue : Znth (Zlength l1) (l1 ++ [a]) default = a := by
        simpa only [Int.sub_self, AUXLib.Znth] using happLast
      exact hvalue.symm.trans hlast
  · rintro ⟨hlt, ⟨⟨hlen, hnth⟩, ha⟩⟩
    change AUXLib.Zlength l1 < AUXLib.Zlength l2 at hlt
    change AUXLib.Zlength l1 <= AUXLib.Zlength l2 at hlen
    change (forall i, 0 <= i /\ i < AUXLib.Zlength l1 ->
      AUXLib.Znth i l1 default = AUXLib.Znth i l2 default) at hnth
    change a = AUXLib.Znth (AUXLib.Zlength l1) l2 default at ha
    constructor
    · have happ : Zlength (l1 ++ [a]) = Zlength l1 + 1 := by
        simpa [ListLib.Zlength, AUXLib.Zlength]
      omega
    · intro i hi
      change 0 <= i /\ i < AUXLib.Zlength (l1 ++ [a]) at hi
      by_cases hil : i < Zlength l1
      · exact (ListLib.app_Znth1 default l1 [a] i ⟨hi.1, hil⟩).trans
          (hnth i ⟨hi.1, hil⟩)
      · have hnonneg := AUXLib.Zlength_nonneg l1
        have hieq : i = Zlength l1 := by
          have happ : Zlength (l1 ++ [a]) = Zlength l1 + 1 := by
            simpa [ListLib.Zlength, AUXLib.Zlength]
          omega
        subst i
        have happLast := ListLib.app_Znth2 default l1 [a] (Zlength l1)
          (by omega)
        have hvalue : Znth (Zlength l1) (l1 ++ [a]) default = a := by
          simpa only [Int.sub_self, AUXLib.Znth] using happLast
        exact hvalue.trans ha

theorem prefix_trans {A : Type} (l1 l2 l3 : List A) :
    is_prefix l1 l2 -> is_prefix l2 l3 -> is_prefix l1 l3 := by
  rintro ⟨r1, rfl⟩ ⟨r2, rfl⟩
  exact ⟨r1 ++ r2, by simp [List.append_assoc]⟩

theorem suffix_trans {A : Type} (l1 l2 l3 : List A) :
    is_suffix l1 l2 -> is_suffix l2 l3 -> is_suffix l1 l3 := by
  rintro ⟨r1, rfl⟩ ⟨r2, rfl⟩
  exact ⟨r2 ++ r1, by simp [List.append_assoc]⟩

theorem presuffix_trans {A : Type} (l1 l2 l3 : List A) :
    presuffix l1 l2 -> presuffix l2 l3 -> presuffix l1 l3 := by
  rintro ⟨hp12, hs12⟩ ⟨hp23, hs23⟩
  exact ⟨prefix_trans l1 l2 l3 hp12 hp23, suffix_trans l1 l2 l3 hs12 hs23⟩

theorem prefix_total_order {A : Type} (l1 l2 l : List A) :
    is_prefix l1 l -> is_prefix l2 l -> Zlength l1 <= Zlength l2 ->
      is_prefix l1 l2 := by
  intro h1 h2 hlen
  rw [prefix_iff'] at h1 h2 ⊢
  refine ⟨hlen, ?_⟩
  intro default i hi
  have hi2 : i < Zlength l2 := by omega
  exact (h1.2 default i hi).trans
    (h2.2 default i ⟨hi.1, hi2⟩).symm

theorem suffix_total_order {A : Type} (l1 l2 l : List A) :
    is_suffix l1 l -> is_suffix l2 l -> Zlength l1 <= Zlength l2 ->
      is_suffix l1 l2 := by
  intro h1 h2 hlen
  rw [suffix_iff'] at h1 h2 ⊢
  refine ⟨hlen, ?_⟩
  intro default i hi
  have hi2 : i < Zlength l2 := by omega
  exact (h1.2 default i hi).trans
    (h2.2 default i ⟨hi.1, hi2⟩).symm

theorem partial_match_result_total_order {A : Type}
    (l1 l2 patn text : List A) :
    partial_match_result patn text l1 ->
    partial_match_result patn text l2 ->
    Zlength l1 <= Zlength l2 -> presuffix l1 l2 := by
  rintro ⟨hs1, hp1⟩ ⟨hs2, hp2⟩ hlen
  exact ⟨prefix_total_order l1 l2 patn hp1 hp2 hlen,
    suffix_total_order l1 l2 text hs1 hs2 hlen⟩

theorem partial_match_result_iff {A : Type} (res0 patn text : List A)
    (hbest : best_partial_match_result patn text res0) (res : List A) :
    partial_match_result patn text res <-> presuffix res res0 := by
  constructor
  · intro hres
    exact partial_match_result_total_order res res0 patn text hres hbest.1
      (hbest.2 res hres)
  · rintro ⟨hp, hs⟩
    exact ⟨suffix_trans res res0 text hs hbest.1.1,
      prefix_trans res res0 patn hp hbest.1.2⟩

theorem partial_match_result_snoc_iff {A : Type} (default : A)
    (res patn text : List A) (ch : A) :
    partial_match_result patn (text ++ [ch]) res <->
      res = [] \/
      exists res', res = res' ++ [ch] /\
        Zlength res' < Zlength patn /\
        Znth (Zlength res') patn default = ch /\
        partial_match_result patn text res' := by
  constructor
  · intro h
    rcases List.eq_nil_or_concat res with rfl | ⟨res', ch0, rfl⟩
    · exact Or.inl rfl
    · simp only [List.concat_eq_append] at h ⊢
      have hs := (is_suffix_snoc_snoc_iff res' text ch0 ch).mp h.1
      have hp := h.2
      refine Or.inr ⟨res', ?_, ?_, ?_, ?_⟩
      · rw [hs.2]
      · have hplen := prefix_Zlength (res' ++ [ch0]) patn hp
        have happ := AUXLib.Zlength_app res' [ch0]
        have hone : AUXLib.Zlength [ch0] = 1 := rfl
        omega
      · rcases hp with ⟨tail, rfl⟩
        rw [hs.2]
        simp [AUXLib.Znth, AUXLib.Zlength]
      · refine ⟨hs.1, ?_⟩
        exact prefix_trans res' (res' ++ [ch0]) patn
          ⟨[ch0], rfl⟩ h.2
  · rintro (rfl | ⟨res', rfl, hlen, hnth, hpartial⟩)
    · exact ⟨⟨text ++ [ch], by simp⟩, ⟨patn, rfl⟩⟩
    · exact ⟨(is_suffix_snoc_snoc_iff res' text ch ch).mpr
          ⟨hpartial.1, rfl⟩,
        (is_prefix_snoc_iff default res' patn ch).mpr
          ⟨hlen, hpartial.2, hnth.symm⟩⟩

theorem sublist_one_ele {A : Type} (i : Int) (text : List A)
    (ch default : A) (hi : 0 <= i /\ i < Zlength text)
    (hch : ch = Znth i text default) :
    sublist 0 i text ++ [ch] = sublist 0 (i + 1) text := by
  rw [AUXLib.sublist_split 0 (i + 1) i text
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  congr 1
  exact (congrArg (fun x => [x]) hch).trans
    (ListLib.sublist_one_ele default text i hi).symm

theorem sublist_one_ele' {A : Type} (i : Int) (text : List A)
    (default : A) (hi : 0 <= i /\ i < Zlength text) :
    sublist 0 (i + 1) text = sublist 0 i text ++ [Znth i text default] := by
  exact (sublist_one_ele i text (Znth i text default) default hi rfl).symm

theorem sublist_single' {A : Type} (n : Int) (l : List A) (a : A)
    (hn : 0 < n /\ n <= Int.ofNat l.length) :
    sublist (n - 1) n l = [Znth (n - 1) l a] := by
  have h := AUXLib.sublist_single a (n - 1) l (by
    change 0 <= n - 1 /\ n - 1 < AUXLib.Zlength l
    simp only [AUXLib.Zlength]
    omega)
  have heq : n - 1 + 1 = n := by omega
  simpa only [heq] using h

theorem prefix_iff_sublist {A : Type} (l1 l2 : List A) :
    is_prefix l1 l2 <->
      exists j, 0 <= j /\ j <= Zlength l2 /\ l1 = sublist 0 j l2 := by
  constructor
  · rintro ⟨tail, rfl⟩
    refine ⟨Zlength l1, AUXLib.Zlength_nonneg l1, ?_, ?_⟩
    · have h := AUXLib.Zlength_app l1 tail
      have ht := AUXLib.Zlength_nonneg tail
      omega
    · symm
      have hsub := ListLib.sublist_split_app_l 0 (Zlength l1) l1 tail
        ⟨by omega, AUXLib.Zlength_nonneg l1⟩ (Int.le_refl _)
      change AUXLib.sublist 0 (AUXLib.Zlength l1) (l1 ++ tail) =
        AUXLib.sublist 0 (AUXLib.Zlength l1) l1 at hsub
      rw [hsub]
      exact AUXLib.sublist_self l1 (Zlength l1) rfl
  · rintro ⟨j, hj0, hjlen, rfl⟩
    refine ⟨sublist j (Zlength l2) l2, ?_⟩
    rw [← AUXLib.sublist_split 0 (Zlength l2) j l2
      ⟨by omega, hj0⟩ ⟨hjlen, Int.le_refl _⟩]
    exact (AUXLib.sublist_self l2 (Zlength l2) rfl).symm

theorem nil_prefix {A : Type} (l : List A) : is_prefix [] l := by
  exact ⟨l, rfl⟩

theorem nil_suffix {A : Type} (l : List A) : is_suffix [] l := by
  exact ⟨l, by simp⟩

theorem nil_presuffix {A : Type} (l : List A) : presuffix [] l := by
  exact ⟨nil_prefix l, nil_suffix l⟩

theorem partial_match_nil {A : Type} (patn text : List A) :
    partial_match_result patn text [] := by
  exact ⟨nil_suffix text, nil_prefix patn⟩

theorem Zlength_nonnil {A : Type} (l : List A) :
    Not (l = []) <-> Zlength l > 0 := by
  cases l with
  | nil => simp
  | cons a l =>
      simp [ListLib.Zlength, AUXLib.Zlength]

def jrange {B : Type} (j : Int) (array : List B) : Prop :=
  0 <= j /\ j < Zlength array

theorem inner_jrange_inv {A : Type} (default : A) (patn text : List A)
    (vnext : List Int) (i j : Int)
    (hlen : Zlength vnext <= Zlength patn)
    (hvnext : forall i0, 0 <= i0 /\ i0 < Zlength vnext ->
      0 <= Znth i0 vnext 0 /\ Znth i0 vnext 0 < Zlength vnext)
    (hj : jrange j vnext) :
    Hoare (fun _ : Unit => True)
      (x <- inner_body default patn vnext (Znth i text default) j ;;
        continue_case x)
      (fun j' _ => jrange j' vnext) := by
  unfold inner_body
  hoare_auto <;> try (unfold jrange at *; omega)
  have hnext := hvnext (j - 1) (by
    unfold jrange at hj
    omega)
  unfold jrange at *
  omega

theorem inner_pre_derive_jrange {A : Type} (patn : List A)
    (vnext : List Int) (hfunc : is_prefix_func vnext patn) :
    forall i0, 0 <= i0 /\ i0 < Zlength vnext ->
      0 <= Znth i0 vnext 0 /\ Znth i0 vnext 0 < Zlength vnext := by
  intro i0 hi
  have h := hfunc i0 hi
  omega

theorem inner_jrange_brk1 {B : Type} (vnext : List B) (j : Int)
    (hj : jrange j vnext) : 0 <= j + 1 /\ j + 1 <= Zlength vnext := by
  unfold jrange at hj
  omega

theorem inner_jrange_brk2 {B : Type} (vnext : List B) :
    0 <= (0 : Int) /\ 0 <= Zlength vnext := by
  exact ⟨by omega, AUXLib.Zlength_nonneg vnext⟩

theorem constr_pre_jrange : jrange 0 ([0] : List Int) := by
  simp [jrange, AUXLib.Zlength]

theorem constr_inner_post_jrange (vnext : List Int) (j : Int)
    (hj : 0 <= j /\ j <= Zlength vnext) :
    jrange j (vnext ++ [j]) := by
  unfold jrange
  have happ := AUXLib.Zlength_app vnext [j]
  have hone : Zlength [j] = 1 := rfl
  omega

theorem match_pre_jrange {A : Type} (patn : List A) (vnext : List Int)
    (hpatn : Not (patn = [])) (hlen : Zlength vnext = Zlength patn) :
    jrange 0 vnext := by
  have hp := (Zlength_nonnil patn).mp hpatn
  unfold jrange
  omega

theorem match_inner_post_jrange {A : Type} (patn : List A)
    (vnext : List Int) (j : Int) (hlen : Zlength vnext = Zlength patn)
    (hj : 0 <= j /\ j <= Zlength vnext) (hlt : j < Zlength patn) :
    jrange j vnext := by
  unfold jrange
  omega

theorem presuffix_nil_iff {A : Type} (l : List A) :
    presuffix l [] <-> l = [] := by
  constructor
  · intro h
    rcases h.1 with ⟨r, hr⟩
    have hlen : 0 = l.length + r.length := by
      simpa only [List.length_nil, List.length_append] using congrArg List.length hr
    exact List.eq_nil_of_length_eq_zero (by omega)
  · rintro rfl
    exact nil_presuffix []

theorem prefix_app_iff {A : Type} (l1 l2 l3 : List A) :
    is_prefix l1 l2 <->
      Zlength l1 <= Zlength l2 /\ is_prefix l1 (l2 ++ l3) := by
  constructor
  · intro h
    refine ⟨prefix_Zlength l1 l2 h, ?_⟩
    rcases h with ⟨tail, rfl⟩
    exact ⟨tail ++ l3, by simp [List.append_assoc]⟩
  · rintro ⟨hlen, hprefix⟩
    rw [prefix_iff'] at hprefix ⊢
    refine ⟨hlen, ?_⟩
    intro default i hi
    change AUXLib.Zlength l1 <= AUXLib.Zlength l2 at hlen
    change 0 <= i /\ i < AUXLib.Zlength l1 at hi
    have hi2 : i < AUXLib.Zlength l2 := by omega
    have happ := ListLib.app_Znth1 default l2 l3 i
      ⟨hi.1, hi2⟩
    exact (hprefix.2 default i hi).trans happ

theorem suffix_app_iff {A : Type} (l1 l2 l3 : List A) :
    is_suffix l1 l2 <->
      Zlength l1 <= Zlength l2 /\ is_suffix l1 (l3 ++ l2) := by
  constructor
  · intro h
    refine ⟨suffix_Zlength l1 l2 h, ?_⟩
    rcases h with ⟨head, rfl⟩
    exact ⟨l3 ++ head, by simp [List.append_assoc]⟩
  · rintro ⟨hlen, hsuffix⟩
    rw [suffix_iff'] at hsuffix ⊢
    refine ⟨hlen, ?_⟩
    intro default i hi
    have htotal := AUXLib.Zlength_app l3 l2
    have hidx : AUXLib.Zlength (l3 ++ l2) - 1 - i >=
        AUXLib.Zlength l3 := by omega
    have happ := ListLib.app_Znth2 default l3 l2
      (AUXLib.Zlength (l3 ++ l2) - 1 - i) hidx
    have heq : AUXLib.Zlength (l3 ++ l2) - 1 - i - AUXLib.Zlength l3 =
        AUXLib.Zlength l2 - 1 - i := by omega
    rw [heq] at happ
    exact (hsuffix.2 default i hi).trans happ

theorem prefix_sublist_iff {A : Type} (l0 l : List A) (i : Int)
    (hi : 0 <= i /\ i <= Zlength l) :
    is_prefix l0 (sublist 0 i l) <->
      Zlength l0 <= i /\ is_prefix l0 l := by
  have hlen : Zlength (sublist 0 i l) = i := by
    simpa using ListLib.Zlength_sublist 0 i l
      ⟨by omega, hi.1⟩ hi.2
  have hsub : is_prefix (sublist 0 i l) l := by
    refine ⟨sublist i (Zlength l) l, ?_⟩
    rw [← AUXLib.sublist_split 0 (Zlength l) i l
      ⟨by omega, hi.1⟩ ⟨hi.2, Int.le_refl _⟩]
    exact (AUXLib.sublist_self l (Zlength l) rfl).symm
  constructor
  · intro h
    exact ⟨by have := prefix_Zlength l0 (sublist 0 i l) h; omega,
      prefix_trans l0 (sublist 0 i l) l h hsub⟩
  · rintro ⟨hlen0, hp⟩
    apply prefix_total_order l0 (sublist 0 i l) l hp hsub
    omega

theorem suffix_sublist_cons_iff {A : Type} (l0 l : List A) (i : Int)
    (hi : 1 <= i /\ i <= Zlength l) :
    is_suffix l0 (sublist 1 i l) <->
      Zlength l0 <= i - 1 /\ is_suffix l0 (sublist 0 i l) := by
  have hlen : Zlength (sublist 1 i l) = i - 1 := by
    exact ListLib.Zlength_sublist 1 i l ⟨by omega, hi.1⟩ hi.2
  have hsplit := AUXLib.sublist_split 0 i 1 l
    ⟨by omega, by omega⟩ ⟨hi.1, hi.2⟩
  have hsub : is_suffix (sublist 1 i l) (sublist 0 i l) :=
    ⟨sublist 0 1 l, hsplit⟩
  constructor
  · intro h
    exact ⟨by have := suffix_Zlength l0 (sublist 1 i l) h; omega,
      suffix_trans l0 (sublist 1 i l) (sublist 0 i l) h hsub⟩
  · rintro ⟨hlen0, hs⟩
    apply suffix_total_order l0 (sublist 1 i l) (sublist 0 i l) hs hsub
    omega

theorem max_proper_best_partial {A : Type} (l : List A) (i j : Int)
    (hi : 1 <= i /\ i <= Zlength l) :
    max_proper_presuffix (sublist 0 j l) (sublist 0 i l) <->
      best_partial_match_result l (sublist 1 i l) (sublist 0 j l) := by
  let lj := sublist 0 j l
  let li0 := sublist 0 i l
  let li1 := sublist 1 i l
  have hli0 : Zlength li0 = i := by
    dsimp [li0]
    simpa using ListLib.Zlength_sublist 0 i l
      ⟨by omega, by omega⟩ hi.2
  have hli1 : Zlength li1 = i - 1 := by
    dsimp [li1]
    exact ListLib.Zlength_sublist 1 i l ⟨by omega, hi.1⟩ hi.2
  constructor
  · intro hleft
    change max_proper_presuffix lj li0 at hleft
    rcases hleft with ⟨⟨⟨hpLjLi0, hsLjLi0⟩, hproper⟩, hmax⟩
    have hlenLj : Zlength lj <= i - 1 := by omega
    have hpLjL : is_prefix lj l :=
      ((prefix_sublist_iff lj l i ⟨by omega, hi.2⟩).mp hpLjLi0).2
    have hsLjLi1 : is_suffix lj li1 :=
      (suffix_sublist_cons_iff lj l i hi).mpr ⟨hlenLj, hsLjLi0⟩
    refine ⟨⟨hsLjLi1, hpLjL⟩, ?_⟩
    intro l3 hpartial
    change partial_match_result l li1 l3 at hpartial
    have hs3 := (suffix_sublist_cons_iff l3 l i hi).mp hpartial.1
    have hp3Li0 := (prefix_sublist_iff l3 l i ⟨by omega, hi.2⟩).mpr
      ⟨by omega, hpartial.2⟩
    have hproper3 : proper_presuffix l3 li0 :=
      ⟨⟨hp3Li0, hs3.2⟩, by omega⟩
    exact presuffix_Zlength l3 lj (hmax l3 hproper3)
  · intro hright
    change best_partial_match_result l li1 lj at hright
    rcases hright with ⟨⟨hsLjLi1, hpLjL⟩, hmax⟩
    have hsLj := (suffix_sublist_cons_iff lj l i hi).mp hsLjLi1
    have hpLj := (prefix_sublist_iff lj l i ⟨by omega, hi.2⟩).mpr
      ⟨by omega, hpLjL⟩
    change max_proper_presuffix lj li0
    refine ⟨⟨⟨hpLj, hsLj.2⟩, by omega⟩, ?_⟩
    intro l3 hproper3
    change presuffix l3 li0 /\ Zlength l3 < Zlength li0 at hproper3
    have hp3 := (prefix_sublist_iff l3 l i ⟨by omega, hi.2⟩).mp hproper3.1.1
    have hs3Li1 := (suffix_sublist_cons_iff l3 l i hi).mpr
      ⟨by omega, hproper3.1.2⟩
    have hpartial3 : partial_match_result l li1 l3 := ⟨hs3Li1, hp3.2⟩
    have hlen3 := hmax l3 hpartial3
    exact ⟨prefix_total_order l3 lj l hp3.2 hpLjL hlen3,
      suffix_total_order l3 lj li1 hs3Li1 hsLjLi1 hlen3⟩

theorem sublist_sublist01 {A : Type} (i j : Int) (l : List A)
    (h : 0 <= i /\ i < j) :
    sublist 0 i (sublist 1 j l) = sublist 1 (i + 1) l := by
  exact ListLib.Zsublist_Zsublist i j 0 1 l (by omega)
    ⟨by omega, by omega⟩ (by omega)

theorem suffix_Zlength_inv {A : Type} (l1 l2 : List A)
    (hlen : Zlength l1 = Zlength l2) (hs : is_suffix l1 l2) :
    l1 = l2 := by
  rcases hs with ⟨head, rfl⟩
  have happ := AUXLib.Zlength_app head l1
  have hhead := AUXLib.Zlength_nonneg head
  have hzero : Zlength head = 0 := by omega
  have : head = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa [AUXLib.Zlength] using hzero
  simp [this]

theorem best_partial_match_inv {A : Type} (patn text l1 l2 : List A)
    (h1 : best_partial_match_result patn text l1)
    (h2 : best_partial_match_result patn text l2) : l1 = l2 := by
  have h12 := h1.2 l2 h2.1
  have h21 := h2.2 l1 h1.1
  have hs := (partial_match_result_total_order l1 l2 patn text
    h1.1 h2.1 h21).2
  exact suffix_Zlength_inv l1 l2 (by omega) hs

theorem best_partial_match_iff {A : Type} (patn text : List A) (r : Int)
    (hr : 0 <= r /\ r <= Zlength text - Zlength patn) :
    best_partial_match_result patn
        (sublist 0 (r + Zlength patn) text) patn <->
      sublist r (r + Zlength patn) text = patn := by
  have hp0 := AUXLib.Zlength_nonneg patn
  have ht0 := AUXLib.Zlength_nonneg text
  have hend : r + Zlength patn <= Zlength text := by omega
  have hsegLen : Zlength (sublist r (r + Zlength patn) text) =
      Zlength patn := by
    have h := ListLib.Zlength_sublist r (r + Zlength patn) text
      ⟨hr.1, by omega⟩ hend
    change AUXLib.Zlength (AUXLib.sublist r
      (r + AUXLib.Zlength patn) text) =
      r + AUXLib.Zlength patn - r at h
    omega
  constructor
  · intro hbest
    have hsWhole := hbest.1.1
    have hsplit := AUXLib.sublist_split 0 (r + Zlength patn) r text
      ⟨by omega, hr.1⟩ ⟨by omega, hend⟩
    have hsSeg : is_suffix patn (sublist r (r + Zlength patn) text) := by
      apply (suffix_app_iff patn (sublist r (r + Zlength patn) text)
        (sublist 0 r text)).mpr
      refine ⟨by omega, ?_⟩
      rw [← hsplit]
      exact hsWhole
    exact (suffix_Zlength_inv patn
      (sublist r (r + Zlength patn) text) (by omega) hsSeg).symm
  · intro hseg
    refine ⟨?_, ?_⟩
    · constructor
      · refine ⟨sublist 0 r text, ?_⟩
        have hsplit := AUXLib.sublist_split 0 (r + Zlength patn) r text
          ⟨by omega, hr.1⟩ ⟨by omega, hend⟩
        exact hsplit.trans (congrArg (fun xs => sublist 0 r text ++ xs) hseg)
      · exact ⟨[], by simp⟩
    · intro res hres
      exact prefix_Zlength res patn hres.2

def no_occurance {A : Type} (patn text : List A) : Prop :=
  forall i, 0 <= i /\ i <= Zlength text - Zlength patn ->
    Not (sublist i (i + Zlength patn) text = patn)

def first_occur {A : Type} (patn text : List A) (z : Int) : Prop :=
  sublist z (z + Zlength patn) text = patn /\
    no_occurance patn (sublist 0 (z + Zlength patn - 1) text)

def partial_match_inv {A : Type} (patn text : List A) (i j : Int) : Prop :=
  partial_match_result patn (sublist 0 i text) (sublist 0 j patn)

theorem inner_pre_partial_match_inv {A : Type} (patn text : List A)
    (i j : Int)
    (hbest : best_partial_match_result patn (sublist 0 i text)
      (sublist 0 j patn)) : partial_match_inv patn text i j := by
  exact hbest.1

theorem inner_partial_match_inv {A : Type} (default : A)
    (patn text : List A) (vnext : List Int) (i jPre j : Int)
    (hlen : Zlength vnext <= Zlength patn)
    (hfunc : is_prefix_func vnext patn)
    (hbest : best_partial_match_result patn (sublist 0 i text)
      (sublist 0 jPre patn))
    (hj : jrange j vnext)
    (hpartial : partial_match_inv patn text i j) :
    Hoare (fun _ : Unit => True)
      (x <- inner_body default patn vnext (Znth i text default) j ;;
        continue_case x)
      (fun j' _ => partial_match_inv patn text i j') := by
  unfold inner_body
  hoare_auto <;> try (unfold jrange partial_match_inv at *; omega)
  have hf := hfunc (j - 1) (by
    unfold jrange at hj
    omega)
  have hjSucc : j - 1 + 1 = j := by omega
  rw [hjSucc] at hf
  let next := Znth (j - 1) vnext 0
  have hfPresuffix : presuffix (sublist 0 next patn)
      (sublist 0 j patn) := by
    simpa only [show j - 1 + 1 = j by omega] using hf.2.2.1.1
  have hpresuffix : presuffix (sublist 0 next patn)
      (sublist 0 jPre patn) := by
    have hp := (partial_match_result_iff
      (sublist 0 jPre patn) patn (sublist 0 i text) hbest
      (sublist 0 j patn)).mp hpartial
    exact presuffix_trans _ _ _ hfPresuffix hp
  have hpartial' := (partial_match_result_iff
    (sublist 0 jPre patn) patn (sublist 0 i text) hbest
    (sublist 0 next patn)).mpr hpresuffix
  exact hpartial'

def presuffix_inv {A : Type} (default : A) (patn text : List A)
    (i j : Int) : Prop :=
  forall j0, 0 < j0 /\ j0 <= Zlength patn ->
    (partial_match_result patn (sublist 0 (i + 1) text)
        (sublist 0 j0 patn) <->
      Znth (j0 - 1) patn default = Znth i text default /\
        presuffix (sublist 0 (j0 - 1) patn) (sublist 0 j patn))

theorem inner_pre_presuffix_inv {A : Type} (default : A)
    (patn text : List A) (vnext : List Int) (i j : Int)
    (hlen : Zlength vnext <= Zlength patn)
    (hi : 0 <= i /\ i < Zlength text)
    (hbest : best_partial_match_result patn (sublist 0 i text)
      (sublist 0 j patn)) : presuffix_inv default patn text i j := by
  intro j0 hj0
  rw [sublist_one_ele' i text default hi]
  rw [partial_match_result_snoc_iff default]
  have hjLen : Zlength (sublist 0 j0 patn) = j0 := by
    simpa using ListLib.Zlength_sublist 0 j0 patn
      ⟨by omega, by omega⟩ hj0.2
  constructor
  · intro hmatch
    rcases hmatch with hempty | ⟨res, hres, hresLen, hchar, hpartial⟩
    · have hz : Zlength (sublist 0 j0 patn) = 0 := by rw [hempty]; rfl
      omega
    · have hresZ : Zlength res = j0 - 1 := by
        have happ := AUXLib.Zlength_app res [Znth i text default]
        have hone : Zlength [Znth i text default] = 1 := rfl
        rw [hres] at hjLen
        omega
      have hsplit := AUXLib.sublist_split 0 j0 (j0 - 1) patn
        ⟨by omega, by omega⟩ ⟨by omega, hj0.2⟩
      have hsingle := sublist_single' j0 patn default
        ⟨hj0.1, by simpa [AUXLib.Zlength] using hj0.2⟩
      have hchar' : Znth (j0 - 1) patn default = Znth i text default := by
        rw [← hresZ]
        exact hchar
      have hprefix : sublist 0 (j0 - 1) patn = res := by
        apply List.append_cancel_right
        calc
          sublist 0 (j0 - 1) patn ++ [Znth i text default] =
              sublist 0 (j0 - 1) patn ++
                [Znth (j0 - 1) patn default] := by
                  rw [hchar']
          _ = sublist 0 j0 patn := by rw [← hsingle, ← hsplit]
          _ = res ++ [Znth i text default] := hres
      constructor
      · exact hchar'
      · rw [hprefix]
        exact (partial_match_result_iff (sublist 0 j patn) patn
          (sublist 0 i text) hbest res).mp hpartial
  · rintro ⟨hchar, hpresuffix⟩
    refine Or.inr ⟨sublist 0 (j0 - 1) patn, ?_, ?_, ?_, ?_⟩
    · rw [AUXLib.sublist_split 0 j0 (j0 - 1) patn
        ⟨by omega, by omega⟩ ⟨by omega, hj0.2⟩]
      rw [sublist_single' j0 patn default
        ⟨hj0.1, by simpa [AUXLib.Zlength] using hj0.2⟩]
      rw [hchar]
    · have hsubLen := ListLib.Zlength_sublist 0 (j0 - 1) patn
        ⟨by omega, by omega⟩ (by
          change j0 - 1 <= AUXLib.Zlength patn
          omega)
      change AUXLib.Zlength (AUXLib.sublist 0 (j0 - 1) patn) =
        j0 - 1 - 0 at hsubLen
      omega
    · have hsubLen := ListLib.Zlength_sublist 0 (j0 - 1) patn
        ⟨by omega, by omega⟩ (by
          change j0 - 1 <= AUXLib.Zlength patn
          omega)
      change AUXLib.Zlength (AUXLib.sublist 0 (j0 - 1) patn) =
        j0 - 1 - 0 at hsubLen
      rw [hsubLen]
      simpa using hchar
    · exact (partial_match_result_iff (sublist 0 j patn) patn
        (sublist 0 i text) hbest (sublist 0 (j0 - 1) patn)).mpr hpresuffix

theorem inner_presuffix_inv {A : Type} (default : A)
    (patn text : List A) (vnext : List Int) (i j : Int)
    (hlen : Zlength vnext <= Zlength patn)
    (hfunc : is_prefix_func vnext patn)
    (hj : jrange j vnext)
    (hinv : presuffix_inv default patn text i j) :
    Hoare (fun _ : Unit => True)
      (x <- inner_body default patn vnext (Znth i text default) j ;;
        continue_case x)
      (fun j' _ => presuffix_inv default patn text i j') := by
  unfold inner_body
  hoare_auto <;> try (unfold jrange at hj; omega)
  have hf := hfunc (j - 1) (by
    unfold jrange at hj
    omega)
  have hnextRange : 0 <= Znth (j - 1) vnext 0 := hf.1
  have hjSucc : j - 1 + 1 = j := by omega
  rw [hjSucc] at hf
  unfold presuffix_inv at hinv
  rename_i hjPat hjNext hcharNe hjNe s hs
  unfold presuffix_inv
  intro j0 hj0
  rw [hinv j0 hj0]
  constructor
  · rintro ⟨hchar, hpre⟩
    refine ⟨hchar, ?_⟩
    by_cases heq : j0 - 1 = j
    · exfalso
      apply hcharNe
      simpa [heq] using hchar.symm
    · apply hf.2.2.2
      refine ⟨hpre, ?_⟩
      have hj0Len := ListLib.Zlength_sublist 0 (j0 - 1) patn
        ⟨by omega, by omega⟩ (by
          change j0 - 1 <= AUXLib.Zlength patn
          omega)
      have hjLen := ListLib.Zlength_sublist 0 j patn
        ⟨by omega, by omega⟩ (by
          change j <= AUXLib.Zlength patn
          unfold jrange at hj
          omega)
      change AUXLib.Zlength (AUXLib.sublist 0 (j0 - 1) patn) =
        j0 - 1 - 0 at hj0Len
      change AUXLib.Zlength (AUXLib.sublist 0 j patn) = j - 0 at hjLen
      have hle := presuffix_Zlength _ _ hpre
      omega
  · rintro ⟨hchar, hpre⟩
    refine ⟨hchar, presuffix_trans _ _ _ hpre ?_⟩
    exact hf.2.2.1.1

def inner_inv {A : Type} (default : A) (patn text : List A)
    (vnext : List Int) (i j : Int) : Prop :=
  jrange j vnext /\ partial_match_inv patn text i j /\
    presuffix_inv default patn text i j

theorem inner_body_prop_brk1 {A : Type} (default : A)
    (patn text : List A) (vnext : List Int) (i j : Int)
    (hinv : inner_inv default patn text vnext i j)
    (hlen : Zlength vnext <= Zlength patn)
    (hi : 0 <= i /\ i < Zlength text)
    (hchar : Znth i text default = Znth j patn default) :
    (0 <= j + 1 /\ j + 1 <= Zlength vnext) /\
      best_partial_match_result patn (sublist 0 (i + 1) text)
        (sublist 0 (j + 1) patn) := by
  rcases hinv with ⟨hj, hpartial, hpresuffix⟩
  have hjPat : 0 <= j /\ j < Zlength patn := by
    unfold jrange at hj
    omega
  refine ⟨inner_jrange_brk1 vnext j hj, ?_⟩
  constructor
  · rw [sublist_one_ele' i text default hi]
    rw [sublist_one_ele' j patn default hjPat]
    rw [partial_match_result_snoc_iff default]
    refine Or.inr ⟨sublist 0 j patn, ?_, ?_, ?_, hpartial⟩
    · rw [hchar]
    · have hjLen := ListLib.Zlength_sublist 0 j patn
        ⟨by omega, hjPat.1⟩ (by
          change j <= AUXLib.Zlength patn
          omega)
      change AUXLib.Zlength (AUXLib.sublist 0 j patn) = j - 0 at hjLen
      omega
    · have hjLen := ListLib.Zlength_sublist 0 j patn
        ⟨by omega, hjPat.1⟩ (by
          change j <= AUXLib.Zlength patn
          omega)
      change AUXLib.Zlength (AUXLib.sublist 0 j patn) = j - 0 at hjLen
      rw [hjLen]
      simpa using hchar.symm
  · intro res hres
    rcases (prefix_iff_sublist res patn).mp hres.2 with
      ⟨j0, hj00, hj0Pat, rfl⟩
    have hresLen := ListLib.Zlength_sublist 0 j0 patn
      ⟨by omega, hj00⟩ hj0Pat
    change AUXLib.Zlength (AUXLib.sublist 0 j0 patn) = j0 - 0 at hresLen
    by_cases hj0Pos : 0 < j0
    · have hps := (hpresuffix j0 ⟨hj0Pos, hj0Pat⟩).mp hres
      have hshort := presuffix_Zlength _ _ hps.2
      have hjLen := ListLib.Zlength_sublist 0 j patn
        ⟨by omega, hjPat.1⟩ (by
          change j <= AUXLib.Zlength patn
          omega)
      have hj0Len := ListLib.Zlength_sublist 0 (j0 - 1) patn
        ⟨by omega, by omega⟩ (by
          change j0 - 1 <= AUXLib.Zlength patn
          omega)
      change AUXLib.Zlength (AUXLib.sublist 0 j patn) = j - 0 at hjLen
      change AUXLib.Zlength (AUXLib.sublist 0 (j0 - 1) patn) =
        j0 - 1 - 0 at hj0Len
      have hresultLen := ListLib.Zlength_sublist 0 (j + 1) patn
        ⟨by omega, by omega⟩ (by
          change j + 1 <= AUXLib.Zlength patn
          omega)
      change AUXLib.Zlength (AUXLib.sublist 0 (j + 1) patn) =
        j + 1 - 0 at hresultLen
      omega
    · have hj0Zero : j0 = 0 := by omega
      subst j0
      simp [AUXLib.sublist, AUXLib.Zlength]

theorem inner_body_prop_brk2 {A : Type} (default : A)
    (patn text : List A) (vnext : List Int) (i j : Int)
    (hinv : inner_inv default patn text vnext i j)
    (hchar : Not (Znth i text default = Znth j patn default))
    (hjZero : j = 0) :
    (0 <= (0 : Int) /\ 0 <= Zlength vnext) /\
      best_partial_match_result patn (sublist 0 (i + 1) text)
        (sublist 0 0 patn) := by
  subst j
  rw [AUXLib.Zsublist_nil patn 0 0 (by omega)]
  refine ⟨inner_jrange_brk2 vnext, partial_match_nil _ _, ?_⟩
  intro res hres
  rcases (prefix_iff_sublist res patn).mp hres.2 with
    ⟨j0, hj00, hj0Pat, rfl⟩
  by_cases hj0Pos : 0 < j0
  · rcases hinv with ⟨hj, hpartial, hpresuffix⟩
    have hps := (hpresuffix j0 ⟨hj0Pos, hj0Pat⟩).mp hres
    have hshort := presuffix_Zlength _ _ hps.2
    have hj0Len := ListLib.Zlength_sublist 0 (j0 - 1) patn
      ⟨by omega, by omega⟩ (by
        change j0 - 1 <= AUXLib.Zlength patn
        omega)
    change AUXLib.Zlength (AUXLib.sublist 0 (j0 - 1) patn) =
      j0 - 1 - 0 at hj0Len
    have hempty : AUXLib.Zlength (AUXLib.sublist 0 0 patn) = 0 := by
      rw [AUXLib.Zsublist_nil patn 0 0 (by omega)]
      rfl
    have hj0One : j0 = 1 := by omega
    exfalso
    apply hchar
    simpa [hj0One] using hps.1.symm
  · have hj0Zero : j0 = 0 := by omega
    subst j0
    simp [AUXLib.sublist, AUXLib.Zlength]

def inner_pre {A : Type} (patn text : List A) (vnext : List Int)
    (i jPre : Int) : Prop :=
  Zlength vnext <= Zlength patn /\
    is_prefix_func vnext patn /\
    (0 <= i /\ i < Zlength text) /\
    (0 <= jPre /\ jPre < Zlength vnext) /\
    best_partial_match_result patn (sublist 0 i text)
      (sublist 0 jPre patn)

def inner_post {A : Type} (patn text : List A) (vnext : List Int)
    (i j : Int) : Prop :=
  (0 <= j /\ j <= Zlength vnext) /\
    best_partial_match_result patn (sublist 0 (i + 1) text)
      (sublist 0 j patn)

theorem inner_body_prop_inv {A : Type} (default : A)
    (patn text : List A) (vnext : List Int) (i jPre j : Int)
    (hpre : inner_pre patn text vnext i jPre)
    (hinv : inner_inv default patn text vnext i j) :
    Hoare (fun _ : Unit => True)
      (x <- inner_body default patn vnext (Znth i text default) j ;;
        continue_case x)
      (fun j' _ => inner_inv default patn text vnext i j') := by
  unfold inner_pre at hpre
  unfold inner_inv at hinv ⊢
  hoare_conj
  · apply inner_jrange_inv
    · exact hpre.1
    · exact inner_pre_derive_jrange patn vnext hpre.2.1
    · exact hinv.1
  · apply inner_partial_match_inv default patn text vnext i jPre j
    · exact hpre.1
    · exact hpre.2.1
    · exact hpre.2.2.2.2
    · exact hinv.1
    · exact hinv.2.1
  · apply inner_presuffix_inv default patn text vnext i j
    · exact hpre.1
    · exact hpre.2.1
    · exact hinv.1
    · exact hinv.2.2

theorem inner_body_prop_brk {A : Type} (default : A)
    (patn text : List A) (vnext : List Int) (i j : Int)
    (hlen : Zlength vnext <= Zlength patn)
    (hi : 0 <= i /\ i < Zlength text)
    (hinv : inner_inv default patn text vnext i j) :
    Hoare (fun _ : Unit => True)
      (x <- inner_body default patn vnext (Znth i text default) j ;;
        break_case x)
      (fun j' _ => inner_post patn text vnext i j') := by
  unfold inner_body inner_post
  hoare_auto
  · unfold inner_inv jrange at *
    omega
  · unfold inner_inv jrange at *
    omega
  · exact inner_body_prop_brk1 default patn text vnext i j
      hinv hlen hi (by assumption)
  · exact inner_body_prop_brk2 default patn text vnext i j
      hinv (by assumption) (by assumption)

theorem inner_loop_prop {A : Type} (default : A)
    (patn text : List A) (vnext : List Int) (i j : Int)
    (hpre : inner_pre patn text vnext i j) :
    Hoare (fun _ : Unit => True)
      (inner_loop default patn vnext (Znth i text default) j)
      (fun j' _ => inner_post patn text vnext i j') := by
  unfold inner_loop
  apply Hoare_cons_pre
    (fun _ : Unit => inner_inv default patn text vnext i j)
    (fun _ : Unit => True)
  · intro _ _
    refine ⟨?_, inner_pre_partial_match_inv patn text i j ?_, ?_⟩
    · exact hpre.2.2.2.1
    · exact hpre.2.2.2.2
    · exact inner_pre_presuffix_inv default patn text vnext i j
        hpre.1 hpre.2.2.1 hpre.2.2.2.2
  · apply Hoare_repeat_break
      (inner_body default patn vnext (Znth i text default))
      (fun j' _ => inner_inv default patn text vnext i j')
      (fun j' _ => inner_post patn text vnext i j')
    intro j'
    apply Hoare_sum
    · stateless_intros
      exact inner_body_prop_inv default patn text vnext i j j'
        hpre (by assumption)
    · stateless_intros
      exact inner_body_prop_brk default patn text vnext i j'
        hpre.1 hpre.2.2.1 (by assumption)

def constr_inv {A : Type} (patn : List A) (vnext : List Int)
    (i j : Int) : Prop :=
  jrange j vnext /\ Zlength vnext = i /\
    is_prefix_func vnext patn /\ j = Znth (i - 1) vnext 0

theorem constr_pre_derive_inv {A : Type} (patn : List A)
    (hpat : Zlength patn > 0) : constr_inv patn [0] 1 0 := by
  refine ⟨constr_pre_jrange, rfl, ?_, rfl⟩
  intro i0 hi0
  have hiZero : i0 = 0 := by
    change 0 <= i0 /\ i0 < 1 at hi0
    omega
  subst i0
  have hz : Znth 0 ([0] : List Int) 0 = 0 := rfl
  rw [hz]
  refine ⟨by omega, by omega, ?_⟩
  rw [AUXLib.Zsublist_nil patn 0 0 (by omega)]
  refine ⟨⟨nil_presuffix _, ?_⟩, ?_⟩
  · have hlen := ListLib.Zlength_sublist 0 1 patn
      ⟨by omega, by omega⟩ (by
        change 1 <= AUXLib.Zlength patn
        omega)
    change AUXLib.Zlength (AUXLib.sublist 0 1 patn) = 1 - 0 at hlen
    have hlen' : AUXLib.Zlength (AUXLib.sublist 0 (0 + 1) patn) = 1 := by
      simpa using hlen
    have hempty : AUXLib.Zlength ([] : List A) = 0 := rfl
    omega
  · intro l3 hproper
    have hnonneg := AUXLib.Zlength_nonneg l3
    have htargetLen := ListLib.Zlength_sublist 0 1 patn
      ⟨by omega, by omega⟩ (by
        change 1 <= AUXLib.Zlength patn
        omega)
    change AUXLib.Zlength (AUXLib.sublist 0 1 patn) = 1 - 0 at htargetLen
    have htargetLen' :
        AUXLib.Zlength (AUXLib.sublist 0 (0 + 1) patn) = 1 := by
      simpa using htargetLen
    have hstrict := hproper.2
    have hlZero : AUXLib.Zlength l3 = 0 := by omega
    have hlNil : l3 = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [AUXLib.Zlength] using hlZero
    subst l3
    exact nil_presuffix []

theorem constr_inner_spec_pre {A : Type} (patn : List A)
    (vnext : List Int) (i j : Int)
    (hi : 1 <= i /\ i < Zlength patn)
    (hinv : constr_inv patn vnext i j) :
    inner_pre patn (sublist 1 (Zlength patn) patn) vnext (i - 1) j := by
  rcases hinv with ⟨hj, hvlen, hfunc, hjValue⟩
  have hf := hfunc (i - 1) (by
    rw [hvlen]
    omega)
  unfold inner_pre
  refine ⟨by omega, hfunc, ?_, hj, ?_⟩
  · have htextLen := ListLib.Zlength_sublist 1 (Zlength patn) patn
      ⟨by omega, by omega⟩ (by
        change AUXLib.Zlength patn <= AUXLib.Zlength patn
        omega)
    change AUXLib.Zlength
      (AUXLib.sublist 1 (AUXLib.Zlength patn) patn) =
      AUXLib.Zlength patn - 1 at htextLen
    omega
  · rw [sublist_sublist01 (i - 1) (Zlength patn) patn (by omega)]
    have hiSucc : i - 1 + 1 = i := by omega
    rw [hiSucc]
    have hfMax := hf.2.2
    rw [hiSucc] at hfMax
    rw [← hjValue] at hfMax
    exact (max_proper_best_partial patn i j ⟨hi.1, by omega⟩).mp hfMax

theorem constr_inner_spec_post {A : Type} (patn : List A)
    (vnext : List Int) (i j j' : Int)
    (hi : 1 <= i /\ i < Zlength patn)
    (hinv : constr_inv patn vnext i j)
    (hpost : inner_post patn (sublist 1 (Zlength patn) patn)
      vnext (i - 1) j') :
    jrange j' (vnext ++ [j']) /\
      is_prefix_func (vnext ++ [j']) patn := by
  rcases hinv with ⟨hj, hvlen, hfunc, hjValue⟩
  refine ⟨constr_inner_post_jrange vnext j' hpost.1, ?_⟩
  intro i0 hi0
  have happLen := AUXLib.Zlength_app vnext [j']
  have hone : AUXLib.Zlength [j'] = 1 := rfl
  by_cases hiOld : i0 < i
  · have hiVnext : 0 <= i0 /\ i0 < Zlength vnext := by
      rw [hvlen]
      exact ⟨hi0.1, hiOld⟩
    have hold := hfunc i0 hiVnext
    have hnth := ListLib.app_Znth1 0 vnext [j'] i0 hiVnext
    change AUXLib.Znth i0 (vnext ++ [j']) 0 =
      AUXLib.Znth i0 vnext 0 at hnth
    rw [hnth]
    exact hold
  · have hiEq : i0 = i := by
      have hi0lt : i0 < AUXLib.Zlength (vnext ++ [j']) := hi0.2
      omega
    subst i0
    have hnth := AUXLib.app_Znth2 0 vnext [j'] i (by
      rw [hvlen]
      omega)
    have hiOffset : i - Zlength vnext = 0 := by omega
    rw [hiOffset] at hnth
    have hnthValue : Znth i (vnext ++ [j']) 0 = j' := by
      simpa [AUXLib.Znth] using hnth
    rw [hnthValue]
    refine ⟨hpost.1.1, ?_, ?_⟩
    · have hjle := hpost.1.2
      omega
    have hbest := hpost.2
    have hiBase : i - 1 + 1 = i := by omega
    rw [hiBase] at hbest
    rw [sublist_sublist01 i (Zlength patn) patn (by omega)] at hbest
    exact (max_proper_best_partial patn (i + 1) j'
      ⟨by omega, by omega⟩).mpr hbest

theorem inner_loop_prop_vnext {A : Type} (default : A)
    (patn : List A) (vnext : List Int) (i j : Int)
    (hi : 1 <= i /\ i < Zlength patn)
    (hinv : constr_inv patn vnext i j) :
    Hoare (fun _ : Unit => True)
      (inner_loop default patn vnext (Znth i patn default) j)
      (fun j' _ => jrange j' (vnext ++ [j']) /\
        is_prefix_func (vnext ++ [j']) patn) := by
  have hchar := AUXLib.Znth_sublist default 1 (i - 1)
    (Zlength patn) patn (by omega) (by omega)
  have hiIndex : i - 1 + 1 = i := by omega
  rw [hiIndex] at hchar
  rw [← hchar]
  apply Hoare_cons_post
    (fun _ : Unit => True)
    (inner_loop default patn vnext
      (Znth (i - 1) (sublist 1 (Zlength patn) patn) default) j)
    (fun j' _ => inner_post patn (sublist 1 (Zlength patn) patn)
      vnext (i - 1) j')
  · intro j' _ hpost
    exact constr_inner_spec_post patn vnext i j j' hi hinv hpost
  · exact inner_loop_prop default patn
      (sublist 1 (Zlength patn) patn) vnext (i - 1) j
      (constr_inner_spec_pre patn vnext i j hi hinv)

theorem constr_body_prop {A : Type} (default : A) (patn : List A)
    (vnext : List Int) (i j : Int)
    (hi : 1 <= i /\ i < Zlength patn)
    (hinv : constr_inv patn vnext i j) :
    Hoare (fun _ : Unit => True)
      (constr_body default patn i (vnext, j))
      (fun res _ => constr_inv patn res.1 (i + 1) res.2) := by
  unfold constr_body
  hoare_step
  · exact hi.2
  ·
    apply Hoare_bind
    · exact inner_loop_prop_vnext default patn vnext i j hi hinv
    · intro j'
      hoare_step
      rcases hinv with ⟨hj, hvlen, hfunc, hjValue⟩
      rename_i s hpost
      refine ⟨hpost.1, ?_, hpost.2, ?_⟩
      · change Zlength (vnext ++ [j']) = i + 1
        have happLen := AUXLib.Zlength_app vnext [j']
        have hone : AUXLib.Zlength [j'] = 1 := rfl
        omega
      · have hnth := AUXLib.app_Znth2 0 vnext [j'] i (by
          rw [hvlen]
          omega)
        have hoffset : i - Zlength vnext = 0 := by omega
        rw [hoffset] at hnth
        have hnthValue : Znth i (vnext ++ [j']) 0 = j' := by
          simpa [AUXLib.Znth] using hnth
        simpa only [show i + 1 - 1 = i by omega] using hnthValue.symm

theorem constr_loop_sound {A : Type} (default : A) (patn : List A)
    (hpat : Not (patn = [])) :
    Hoare (fun _ : Unit => True)
      (constr_loop default patn)
      (fun vnext _ => is_prefix_func vnext patn /\
        Zlength vnext = Zlength patn) := by
  have hpatLen := (Zlength_nonnil patn).mp hpat
  unfold constr_loop
  apply Hoare_bind
  · apply Hoare_range_iter
      (constr_body default patn)
      (fun _ : Unit => True)
      (fun k res _ => constr_inv patn res.1 k res.2)
      1 (Zlength patn)
    · omega
    · intro _ _
      exact constr_pre_derive_inv patn hpatLen
    · intro k hk res
      apply Hoare_stateless
      intro hinv
      exact constr_body_prop default patn res.1 k res.2 hk hinv
  · intro res
    rcases res with ⟨vnext, j⟩
    hoare_step
    rename_i _ hinv
    exact ⟨hinv.2.2.1, hinv.2.1⟩

def match_pre {A : Type} (patn : List A) (vnext : List Int) : Prop :=
  Zlength vnext = Zlength patn /\
    is_prefix_func vnext patn /\ Not (patn = [])

def match_inv {A : Type} (patn text : List A) (vnext : List Int)
    (i j : Int) : Prop :=
  (0 <= j /\ j < Zlength vnext) /\
    best_partial_match_result patn (sublist 0 i text)
      (sublist 0 j patn) /\
    no_occurance patn (sublist 0 i text)

theorem match_pre_derive_inv {A : Type} (patn text : List A)
    (vnext : List Int) (hpre : match_pre patn vnext) :
    match_inv patn text vnext 0 0 := by
  rcases hpre with ⟨hlen, hfunc, hpat⟩
  unfold match_inv
  refine ⟨match_pre_jrange patn vnext hpat hlen, ?_, ?_⟩
  · rw [AUXLib.Zsublist_nil text 0 0 (by omega)]
    rw [AUXLib.Zsublist_nil patn 0 0 (by omega)]
    refine ⟨partial_match_nil _ _, ?_⟩
    intro res hres
    have hresLen := suffix_Zlength res [] hres.1
    simpa [AUXLib.Zlength] using hresLen
  · intro i hi
    have hpatLen := (Zlength_nonnil patn).mp hpat
    have htextLen : Zlength (sublist 0 0 text) = 0 := by
      rw [AUXLib.Zsublist_nil text 0 0 (by omega)]
      rfl
    omega

theorem match_inv_no_occur {A : Type} (patn text : List A)
    (i a : Int)
    (hi : 0 <= i /\ i < Zlength text)
    (hno : no_occurance patn (sublist 0 i text))
    (ha : 0 <= a /\ a < Zlength patn)
    (hbest : best_partial_match_result patn (sublist 0 (i + 1) text)
      (sublist 0 a patn)) :
    no_occurance patn (sublist 0 (i + 1) text) := by
  intro i0 hi0 hocc
  have hiLen := ListLib.Zlength_sublist 0 i text
    ⟨by omega, hi.1⟩ (by
      change i <= AUXLib.Zlength text
      omega)
  have hiSuccLen := ListLib.Zlength_sublist 0 (i + 1) text
    ⟨by omega, by omega⟩ (by
      change i + 1 <= AUXLib.Zlength text
      omega)
  change AUXLib.Zlength (AUXLib.sublist 0 i text) = i - 0 at hiLen
  change AUXLib.Zlength (AUXLib.sublist 0 (i + 1) text) =
    i + 1 - 0 at hiSuccLen
  by_cases hearly : i0 < i - Zlength patn + 1
  · apply hno i0 (by omega)
    have hnewFlat := ListLib.Zsublist_Zsublist0
      (i0 + Zlength patn) (i + 1) i0 text hi0.1
      ⟨by omega, by omega⟩
    have holdFlat := ListLib.Zsublist_Zsublist0
      (i0 + Zlength patn) i i0 text hi0.1
      ⟨by omega, by omega⟩
    change AUXLib.sublist i0 (i0 + Zlength patn)
      (AUXLib.sublist 0 (i + 1) text) =
      AUXLib.sublist i0 (i0 + Zlength patn) text at hnewFlat
    change AUXLib.sublist i0 (i0 + Zlength patn)
      (AUXLib.sublist 0 i text) =
      AUXLib.sublist i0 (i0 + Zlength patn) text at holdFlat
    rw [hnewFlat] at hocc
    rw [holdFlat]
    exact hocc
  · have hi0Eq : i0 = i - Zlength patn + 1 := by omega
    have hend : i0 + Zlength patn = i + 1 := by omega
    have hnewFlat := ListLib.Zsublist_Zsublist0
      (i0 + Zlength patn) (i + 1) i0 text hi0.1
      ⟨by omega, by omega⟩
    change AUXLib.sublist i0 (i0 + Zlength patn)
      (AUXLib.sublist 0 (i + 1) text) =
      AUXLib.sublist i0 (i0 + Zlength patn) text at hnewFlat
    rw [hnewFlat] at hocc
    have hbestPat := (best_partial_match_iff patn text i0 (by
      constructor <;> omega)).mpr hocc
    rw [hend] at hbestPat
    have heq := best_partial_match_inv patn (sublist 0 (i + 1) text)
      patn (sublist 0 a patn) hbestPat hbest
    have heqLen := congrArg AUXLib.Zlength heq
    have haLen := ListLib.Zlength_sublist 0 a patn
      ⟨by omega, ha.1⟩ (by
        change a <= AUXLib.Zlength patn
        omega)
    change AUXLib.Zlength (AUXLib.sublist 0 a patn) = a - 0 at haLen
    omega

theorem match_body_cnt_prop {A : Type} (default : A)
    (patn text : List A) (vnext : List Int) (i j : Int)
    (hi : 0 <= i /\ i < Zlength text)
    (hpre : match_pre patn vnext)
    (hinv : match_inv patn text vnext i j) :
    Hoare (fun _ : Unit => True)
      (x <- match_body default patn text vnext i j ;; continue_case x)
      (fun z _ => match_inv patn text vnext (i + 1) z) := by
  unfold match_body
  hoare_auto <;> try omega
  hoare_auto
  apply Hoare_bind
    (fun _ : Unit => True)
    (fun z _ => inner_post patn text vnext i z)
    (fun z _ => match_inv patn text vnext (i + 1) z)
    (inner_loop default patn vnext (Znth i text default) j)
  · exact inner_loop_prop default patn text vnext i j
      ⟨by
        have hlen := hpre.1
        omega,
       hpre.2.1, hi, hinv.1, hinv.2.1⟩
  · intro z
    apply Hoare_stateless
    intro hpost
    hoare_auto
    refine ⟨?_, hpost.2, ?_⟩
    · exact match_inner_post_jrange patn vnext z hpre.1 hpost.1
        (by assumption)
    · exact match_inv_no_occur patn text i z hi hinv.2.2
        ⟨hpost.1.1, by assumption⟩ hpost.2

theorem match_body_brk_prop {A : Type} (default : A)
    (patn text : List A) (vnext : List Int) (i j : Int)
    (hi : 0 <= i /\ i < Zlength text)
    (hpre : match_pre patn vnext)
    (hinv : match_inv patn text vnext i j) :
    Hoare (fun _ : Unit => True)
      (x <- match_body default patn text vnext i j ;; break_case x)
      (fun z _ => first_occur patn text z) := by
  unfold match_body
  hoare_auto <;> try omega
  hoare_auto
  apply Hoare_bind
    (fun _ : Unit => True)
    (fun z _ => inner_post patn text vnext i z)
    (fun z _ => first_occur patn text z)
    (inner_loop default patn vnext (Znth i text default) j)
  · exact inner_loop_prop default patn text vnext i j
      ⟨by
        have hlen := hpre.1
        omega,
       hpre.2.1, hi, hinv.1, hinv.2.1⟩
  · intro z
    apply Hoare_stateless
    intro hpost
    prog_nf
    hoare_auto
    unfold first_occur
    let first := i - Zlength patn + 1
    have hz : first = i - Zlength patn + 1 := rfl
    have hzEnd : first + Zlength patn = i + 1 := by omega
    have hresultEq : sublist 0 z patn = patn := by
      have hzPat : z = Zlength patn := by assumption
      rw [hzPat]
      exact AUXLib.sublist_self patn (Zlength patn) rfl
    have hbestPat := hpost.2
    rw [hresultEq] at hbestPat
    have hpSuffixLen := suffix_Zlength patn
      (sublist 0 (i + 1) text) hbestPat.1.1
    have hprefixLen := ListLib.Zlength_sublist 0 (i + 1) text
      ⟨by omega, by omega⟩ (by
        change i + 1 <= AUXLib.Zlength text
        omega)
    change AUXLib.Zlength (AUXLib.sublist 0 (i + 1) text) =
      i + 1 - 0 at hprefixLen
    refine ⟨?_, ?_⟩
    · have hiff := best_partial_match_iff patn text first (by
        constructor <;> omega)
      rw [hzEnd] at hiff
      change sublist first (first + Zlength patn) text = patn
      rw [hzEnd]
      exact hiff.mp hbestPat
    · have hcut : first + Zlength patn - 1 = i := by omega
      rw [hcut]
      exact hinv.2.2

theorem match_body_prop {A : Type} (default : A)
    (patn text : List A) (vnext : List Int) (i j : Int)
    (hi : 0 <= i /\ i < Zlength text)
    (hpre : match_pre patn vnext)
    (hinv : match_inv patn text vnext i j) :
    Hoare (fun _ : Unit => True)
      (match_body default patn text vnext i j)
      (fun res _ => match res with
        | .by_break z => first_occur patn text z
        | .by_continue z => match_inv patn text vnext (i + 1) z) := by
  let hsum := Hoare_sum
    (fun _ : Unit => True)
    (match_body default patn text vnext i j)
    (fun z _ => match_inv patn text vnext (i + 1) z)
    (fun z _ => first_occur patn text z)
    (match_body_cnt_prop default patn text vnext i j hi hpre hinv)
    (match_body_brk_prop default patn text vnext i j hi hpre hinv)
  exact Hoare_cons_post
    (fun _ : Unit => True)
    (match_body default patn text vnext i j)
    _
    (fun res _ => match res with
      | .by_break z => first_occur patn text z
      | .by_continue z => match_inv patn text vnext (i + 1) z)
    (by
      intro res _ h
      cases res <;> exact h)
    hsum

theorem match_loop_sound {A : Type} (default : A)
    (patn text : List A) (vnext : List Int)
    (hpat : Not (patn = []))
    (hlen : Zlength vnext = Zlength patn)
    (hfunc : is_prefix_func vnext patn) :
    Hoare (fun _ : Unit => True)
      (match_loop default patn text vnext)
      (fun res _ => match res with
        | some r => first_occur patn text r
        | none => no_occurance patn text) := by
  unfold match_loop
  apply Hoare_bind
    (fun _ : Unit => True)
    (fun res _ => match res with
      | .by_continue j => match_inv patn text vnext (Zlength text) j
      | .by_break z => first_occur patn text z)
  · let hloop := Hoare_range_iter_break
      (match_body default patn text vnext)
      (fun k j _ => match_inv patn text vnext k j)
      (fun _ : Unit => True)
      (fun z _ => first_occur patn text z)
      0 (Zlength text)
      (AUXLib.Zlength_nonneg text)
      0
      (by
        intro _ _
        exact match_pre_derive_inv patn text vnext ⟨hlen, hfunc, hpat⟩
      )
      (by
        intro k hk j
        apply Hoare_stateless
        intro hinv
        let hbody := match_body_prop default patn text vnext k j hk
          ⟨hlen, hfunc, hpat⟩ hinv
        exact Hoare_cons_post
          (fun _ : Unit => True)
          (match_body default patn text vnext k j)
          _ _
          (by
            intro res _ h
            cases res <;> exact h)
          hbody)
    exact Hoare_cons_post
      (fun _ : Unit => True)
      (range_iter_break 0 (Zlength text)
        (match_body default patn text vnext) 0)
      _
      (fun res _ => match res with
        | .by_continue j => match_inv patn text vnext (Zlength text) j
        | .by_break z => first_occur patn text z)
      (by
        intro res _ h
        cases res <;> exact h)
      hloop
  · intro res
    cases res with
    | by_break z =>
        hoare_step
    | by_continue j =>
        hoare_step
        rename_i _ hinv
        have hno := hinv.2.2
        have hself := AUXLib.sublist_self text (Zlength text) rfl
        rw [hself] at hno
        exact hno

end MonadLib.Examples.kmp
