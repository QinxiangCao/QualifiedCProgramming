import SimpleC.SL.SeparationLogic

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace SimpleC.EE.QCP_demos_LLM.sll_lib

open AUXLib
open CompCert
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance sll_libSacContext : SacContext := ⟨naive_C_Rules⟩

noncomputable abbrev data_addr (p : Int) : addr :=
  addr_notation (LE_arrow_field (RE_const p (FET_alias "list")) "data")

noncomputable abbrev next_addr (p : Int) : addr :=
  addr_notation (LE_arrow_field (RE_const p (FET_alias "list")) "next")

private theorem join_pair_pair_reassoc
    (p d n s pd ns result : SacContext.rules.model)
    (hpd : SacContext.rules.join p d pd)
    (hns : SacContext.rules.join n s ns)
    (hresult : SacContext.rules.join pd ns result) :
    exists dn dns,
      SacContext.rules.join d n dn ∧
      SacContext.rules.join dn s dns ∧
      SacContext.rules.join p dns result := by
  rcases SacContext.rules.toContext.join_assoc p d ns pd result hpd hresult with
    ⟨dns, hdns, hpdns⟩
  have hns' := SacContext.rules.toContext.join_comm n s ns hns
  have hdns' := SacContext.rules.toContext.join_comm d ns dns hdns
  rcases SacContext.rules.toContext.join_assoc s n d ns dns hns' hdns' with
    ⟨dn, hnd, hsdn⟩
  exact ⟨dn, dns,
    SacContext.rules.toContext.join_comm n d dn hnd,
    SacContext.rules.toContext.join_comm s dn dns hsdn,
    hpdns⟩

def sll (x : addr) : List Int -> Assertion
  | [] => “ x = NULL ” && emp
  | a :: l0 =>
      “ x ≠ NULL ” &&
        (EX y : addr,
          store_int naive_C_Rules (data_addr x) a **
          store_ptr naive_C_Rules (next_addr x) y **
          sll y l0)

def sllseg (x y : addr) : List Int -> Assertion
  | [] => “ x = y ” && emp
  | a :: l0 =>
      “ x ≠ NULL ” &&
        (EX z : addr,
          store_int naive_C_Rules (data_addr x) a **
          store_ptr naive_C_Rules (next_addr x) z **
          sllseg z y l0)

def sllbseg (x y : addr) : List Int -> Assertion
  | [] => “ x = y ” && emp
  | a :: l0 =>
      EX z : addr,
        “ z ≠ NULL ” &&
          store_ptr naive_C_Rules x z **
          store_int naive_C_Rules (data_addr z) a **
          sllbseg (next_addr z) y l0

attribute [irreducible] sll sllseg sllbseg

theorem sll_zero (x : addr) (l : List Int) (hx : x = NULL) :
    sll x l |-- “ l = [] ” && emp := by
  subst x
  cases l with
  | nil =>
      rw [sll.eq_1]
      intro state h
      exact ⟨rfl, h.2⟩
  | cons a l =>
      rw [sll.eq_2]
      intro state h
      exact (h.1 rfl).elim

theorem sll_not_zero (x : addr) (l : List Int) (hx : x ≠ NULL) :
    sll x l |--
      EX y : addr, EX a : Int, EX l0 : List Int,
        “ l = a :: l0 ” &&
        store_int naive_C_Rules
          (addr_notation (LE_arrow_field (RE_const x (FET_alias "list")) "data")) a **
        store_ptr naive_C_Rules
          (addr_notation (LE_arrow_field (RE_const x (FET_alias "list")) "next")) y **
        sll y l0 := by
  cases l with
  | nil =>
      rw [sll.eq_1]
      intro state h
      exact (hx h.1).elim
  | cons a l =>
      rw [sll.eq_2]
      intro state h
      rcases h with ⟨_, y, hspatial⟩
      exact ⟨y, a, l, rfl, hspatial⟩

theorem sll_not_zero' (x : addr) (l : List Int) (hx : x ≠ NULL) :
    sll x l |-- “ l ≠ [] ” := by
  cases l with
  | nil =>
      rw [sll.eq_1]
      intro state h
      exact (hx h.1).elim
  | cons a l =>
      rw [sll.eq_2]
      intro _ _
      change a :: l ≠ []
      simp

theorem sllseg_len1 (x : addr) (a : Int) (y : addr) (hx : x ≠ NULL) :
    store_int naive_C_Rules
        (addr_notation (LE_arrow_field (RE_const x (FET_alias "list")) "data")) a **
      store_ptr naive_C_Rules
        (addr_notation (LE_arrow_field (RE_const x (FET_alias "list")) "next")) y |--
      sllseg x y [a] := by
  rw [sllseg.eq_2]
  refine coq_prop_andp_right naive_C_Rules (x ≠ NULL) _ _ ?_ hx
  apply exp_right_exists
  refine ⟨y, ?_⟩
  rw [sllseg.eq_1]
  apply sepcon_cancel_res_emp
  refine coq_prop_andp_right naive_C_Rules (y = y) _ _ ?_ rfl
  exact naive_C_Rules.toContext.derivable1_refl _

theorem sllseg_sllseg (x y z : addr) (l1 l2 : List Int) :
    sllseg x y l1 ** sllseg y z l2 |-- sllseg x z (l1 ++ l2) := by
  induction l1 generalizing x with
  | nil =>
      simp only [List.nil_append]
      rw [sllseg.eq_1]
      intro state h
      rcases h with ⟨left, right, hjoin, hleft, hright⟩
      rcases hleft with ⟨hxy, hunit⟩
      subst x
      have hjoin' := SacContext.rules.toContext.join_comm left right state hjoin
      have hrightState :=
        SacContext.rules.toContext.unit_spec right state left hunit hjoin'
      subst state
      exact hright
  | cons a l1 ih =>
      simp only [List.cons_append]
      rw [sllseg.eq_2, sllseg.eq_2]
      intro state h
      rcases h with ⟨left, right, hjoin, hleft, hright⟩
      rcases hleft with ⟨hx, z0, stores, rest, hstoresRest, hstores, hrec⟩
      rcases SacContext.rules.toContext.join_assoc
          stores rest right left state hstoresRest hjoin with
        ⟨restRight, hrestRight, hstoresResult⟩
      have htail := ih z0 restRight
        ⟨rest, right, hrestRight, hrec, hright⟩
      exact ⟨hx, z0, stores, restRight, hstoresResult, hstores, htail⟩

theorem sllseg_sll (x y : addr) (l1 l2 : List Int) :
    sllseg x y l1 ** sll y l2 |-- sll x (l1 ++ l2) := by
  induction l1 generalizing x with
  | nil =>
      simp only [List.nil_append]
      rw [sllseg.eq_1]
      intro state h
      rcases h with ⟨left, right, hjoin, hleft, hright⟩
      rcases hleft with ⟨hxy, hunit⟩
      subst x
      have hjoin' := SacContext.rules.toContext.join_comm left right state hjoin
      have hrightState :=
        SacContext.rules.toContext.unit_spec right state left hunit hjoin'
      subst state
      exact hright
  | cons a l1 ih =>
      simp only [List.cons_append]
      rw [sllseg.eq_2, sll.eq_2]
      intro state h
      rcases h with ⟨left, right, hjoin, hleft, hright⟩
      rcases hleft with ⟨hx, z0, stores, rest, hstoresRest, hstores, hrec⟩
      rcases SacContext.rules.toContext.join_assoc
          stores rest right left state hstoresRest hjoin with
        ⟨restRight, hrestRight, hstoresResult⟩
      have htail := ih z0 restRight
        ⟨rest, right, hrestRight, hrec, hright⟩
      exact ⟨hx, z0, stores, restRight, hstoresResult, hstores, htail⟩

theorem sllbseg_2_sllseg (x y z : addr) (l : List Int) :
    sllbseg x y l ** store_ptr naive_C_Rules y z |--
      EX y' : addr, store_ptr naive_C_Rules x y' ** sllseg y' z l := by
  induction l generalizing x with
  | nil =>
      rw [sllbseg.eq_1]
      intro state h
      rcases h with ⟨left, right, hjoin, hleft, hstore⟩
      rcases hleft with ⟨hxy, hunit⟩
      subst x
      have hjoin' := SacContext.rules.toContext.join_comm left right state hjoin
      have hrightState :=
        SacContext.rules.toContext.unit_spec right state left hunit hjoin'
      subst state
      rcases SacContext.rules.toContext.unit_join right with
        ⟨unit, hunit, hrightUnit⟩
      refine ⟨z, right, unit, hrightUnit, hstore, ?_⟩
      rw [sllseg.eq_1]
      exact ⟨rfl, hunit⟩
  | cons a l ih =>
      rw [sllbseg.eq_2]
      intro state h
      rcases h with ⟨left, right, hjoin, hleft, hright⟩
      rcases hleft with
        ⟨xv, hxv, stores, tail, hstoresTail, hstores, htail⟩
      rcases SacContext.rules.toContext.join_assoc
          stores tail right left state hstoresTail hjoin with
        ⟨tailRight, htailRight, hstoresResult⟩
      rcases ih _ tailRight ⟨tail, right, htailRight, htail, hright⟩ with
        ⟨next, nextState, segState, hnextSeg, hnext, hseg⟩
      rcases hstores with ⟨ptrState, dataState, hptrData, hptr, hdata⟩
      rcases join_pair_pair_reassoc ptrState dataState nextState segState
          stores tailRight state hptrData hnextSeg hstoresResult with
        ⟨dataNext, bodyState, hdataNext, hbody, hresult⟩
      refine ⟨xv, ptrState, bodyState, hresult, hptr, ?_⟩
      rw [sllseg.eq_2]
      exact ⟨hxv, next, dataNext, segState, hbody,
        ⟨dataState, nextState, hdataNext, hdata, hnext⟩, hseg⟩

theorem sllbseg_len1 (x y : addr) (a : Int) (hy : y ≠ 0) :
    store_ptr naive_C_Rules x y **
      store_int naive_C_Rules
        (addr_notation (LE_arrow_field (RE_const y (FET_alias "list")) "data")) a |--
      sllbseg x
        (addr_notation (LE_arrow_field (RE_const y (FET_alias "list")) "next")) [a] := by
  rw [sllbseg.eq_2]
  apply exp_right_exists
  refine ⟨y, ?_⟩
  refine coq_prop_andp_right naive_C_Rules (y ≠ NULL) _ _ ?_ ?_
  · rw [sllbseg.eq_1]
    apply sepcon_cancel_res_emp
    refine coq_prop_andp_right naive_C_Rules (_ = _) _ _ ?_ rfl
    exact naive_C_Rules.toContext.derivable1_refl _
  · simpa [NULL] using hy

theorem sllbseg_sllbseg (x y z : addr) (l1 l2 : List Int) :
    sllbseg x y l1 ** sllbseg y z l2 |-- sllbseg x z (l1 ++ l2) := by
  induction l1 generalizing x with
  | nil =>
      simp only [List.nil_append]
      rw [sllbseg.eq_1]
      intro state h
      rcases h with ⟨left, right, hjoin, hleft, hright⟩
      rcases hleft with ⟨hxy, hunit⟩
      subst x
      have hjoin' := SacContext.rules.toContext.join_comm left right state hjoin
      have hrightState :=
        SacContext.rules.toContext.unit_spec right state left hunit hjoin'
      subst state
      exact hright
  | cons a l1 ih =>
      simp only [List.cons_append]
      rw [sllbseg.eq_2, sllbseg.eq_2]
      intro state h
      rcases h with ⟨left, right, hjoin, hleft, hright⟩
      rcases hleft with ⟨u, hu, stores, tail, hstoresTail, hstores, htail⟩
      rcases SacContext.rules.toContext.join_assoc
          stores tail right left state hstoresTail hjoin with
        ⟨tailRight, htailRight, hstoresResult⟩
      have hcombined := ih _ tailRight
        ⟨tail, right, htailRight, htail, hright⟩
      exact ⟨u, hu, stores, tailRight, hstoresResult, hstores, hcombined⟩

theorem sllseg_0_sll (x : addr) (l : List Int) :
    sllseg x 0 l |-- sll x l := by
  induction l generalizing x with
  | nil =>
      rw [sllseg.eq_1, sll.eq_1]
      intro _ h
      simpa [NULL] using h
  | cons a l ih =>
      rw [sllseg.eq_2, sll.eq_2]
      intro state h
      rcases h with ⟨hx, z, stores, tail, hjoin, hstores, htail⟩
      exact ⟨hx, z, stores, tail, hjoin, hstores, ih z tail htail⟩

theorem sll_length (x : addr) (l : List Int) :
    sll x l |-- store_align4_n naive_C_Rules (Zlength l * 2) := by
  induction l generalizing x with
  | nil =>
      rw [sll.eq_1]
      intro state h
      exact ⟨[], ⟨rfl, interval_list_nil⟩, h.2⟩
  | cons a l ih =>
      rw [sll.eq_2]
      intro state h
      rcases h with ⟨_, y, stores, tail, hstoresTail, hstores, htail⟩
      rcases hstores with ⟨intState, ptrState, hintPtr, hint, hptr⟩
      have halignInt := store_int_align4 naive_C_Rules _ _ intState hint
      have halignPtr := store_ptr_align4 naive_C_Rules _ _ ptrState hptr
      have halignTail := ih y tail htail
      have halignTwo := store_align4_merge naive_C_Rules 1 1 stores
        ⟨intState, ptrState, hintPtr, halignInt, halignPtr⟩
      have halignAll :=
        store_align4_merge naive_C_Rules (1 + 1) (Zlength l * 2) state
          ⟨stores, tail, hstoresTail, halignTwo, halignTail⟩
      have hlen : 1 + 1 + Zlength l * 2 = Zlength (a :: l) * 2 := by
        rw [Zlength_cons]
        omega
      rw [← hlen]
      exact halignAll

theorem sll_length_max (x : addr) (l : List Int) :
    sll x l |-- “ Zlength l * 2 <= Int.max_unsigned / 4 + 1 ” := by
  intro state h
  exact store_align4_n_valid naive_C_Rules (Zlength l * 2) state
    (sll_length x l state h)

end SimpleC.EE.QCP_demos_LLM.sll_lib

namespace SimpleC.EE.QCP_demos_LLM

export SimpleC.EE.QCP_demos_LLM.sll_lib (data_addr next_addr sll sllseg sllbseg)

end SimpleC.EE.QCP_demos_LLM
