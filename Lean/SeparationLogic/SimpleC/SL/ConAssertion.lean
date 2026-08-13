import SetsClass.SetsClass
import SimpleC.SL.CommonAssertion

namespace SimpleC.SL.ConAssertion

open AUXLib
open CompCert
open SimpleC.SL.Mem
open SimpleC.SL.CommonAssertion
open Unifysl.LogicGenerator.demo932

structure STS : Type 1 where
  token : Type
  STS_state : Type
  Transition : (STS_state × (token -> Prop)) -> (STS_state × (token -> Prop)) -> Prop
  InvownedToken : STS_state -> token -> Prop

abbrev TokenSet (S : STS) : Type := S.token -> Prop

abbrev STS_state_transition (S : STS) : Type :=
  (S.STS_state × TokenSet S) -> (S.STS_state × TokenSet S) -> Prop

structure Lstate (S : STS) : Type where
  s_mem : mem
  s_STS : S.STS_state -> Prop
  s_token : TokenSet S

theorem Lstate_eq_split {S : STS} (left right : Lstate S)
    (hmem : left.s_mem = right.s_mem)
    (hstates : Sets.equiv left.s_STS right.s_STS)
    (htokens : Sets.equiv left.s_token right.s_token) : left = right := by
  cases left with
  | mk leftMem leftStates leftTokens =>
    cases right with
    | mk rightMem rightStates rightTokens =>
      change leftMem = rightMem at hmem
      change Sets.equiv leftStates rightStates at hstates
      change Sets.equiv leftTokens rightTokens at htokens
      have hstates' : leftStates = rightStates := pred_ext1 _ _ _ hstates
      have htokens' : leftTokens = rightTokens := pred_ext1 _ _ _ htokens
      cases hmem
      cases hstates'
      cases htokens'
      rfl

def TokenSet_join {S : STS} (s1 s2 s3 : TokenSet S) : Prop :=
  Sets.equiv s3 (Sets.union s1 s2) ∧
    Sets.equiv (Sets.intersect s1 s2) Sets.empty

def valid_transtion {S : STS}
    (s1 s2 : S.STS_state × TokenSet S) : Prop :=
  exists tokenFrame,
    TokenSet_join (S.InvownedToken s1.1) s1.2 tokenFrame ∧
      TokenSet_join (S.InvownedToken s2.1) s2.2 tokenFrame

def valid_Lstate {S : STS} (state : Lstate S) : Prop :=
  forall stsState, state.s_STS stsState ->
    Sets.equiv (Sets.intersect state.s_token (S.InvownedToken stsState)) Sets.empty

def transtion_disjoint_preserved {S : STS}
    (transition : STS_state_transition S) : Prop :=
  forall s1 s2 token1 token2,
    transition (s1, token1) (s2, token2) ->
      Sets.equiv (Sets.intersect token1 (S.InvownedToken s1)) Sets.empty ∧
      Sets.equiv (Sets.intersect token2 (S.InvownedToken s2)) Sets.empty

def transition_token_preserved {S : STS}
    (transition : STS_state_transition S) : Prop :=
  forall s1 s2 token1 token2 tokenFrame,
    transition (s1, token1) (s2, token2) ->
      (TokenSet_join token1 (S.InvownedToken s1) tokenFrame ↔
        TokenSet_join token2 (S.InvownedToken s2) tokenFrame)

def STS_state_join {S : STS}
    (s1 s2 s3 : S.STS_state -> Prop) : Prop :=
  Sets.equiv s3 (Sets.intersect s1 s2)

def state_join {S : STS} (s1 s2 s3 : Lstate S) : Prop :=
  mem_join s1.s_mem s2.s_mem s3.s_mem ∧
    TokenSet_join s1.s_token s2.s_token s3.s_token ∧
    STS_state_join s1.s_STS s2.s_STS s3.s_STS

theorem valid_state_join {S : STS} (s1 s2 s3 : Lstate S)
    (hjoin : state_join s1 s2 s3)
    (hvalid1 : valid_Lstate s1) (hvalid2 : valid_Lstate s2) :
    valid_Lstate s3 := by
  rcases hjoin with ⟨_, ⟨htokens, _⟩, hstates⟩
  intro stsState hstate3 token
  constructor
  · intro hbad
    have hstate12 := (hstates stsState).mp hstate3
    have htoken12 := (htokens token).mp hbad.1
    rcases htoken12 with htoken1 | htoken2
    · exact ((hvalid1 stsState hstate12.1 token).mp ⟨htoken1, hbad.2⟩).elim
    · exact ((hvalid2 stsState hstate12.2 token).mp ⟨htoken2, hbad.2⟩).elim
  · intro hfalse
    exact hfalse.elim

def rely_closed {S : STS} (state : Lstate S)
    (transition : STS_state_transition S) : Prop :=
  forall s1 s2,
    state.s_STS s1 ->
    transition
      (s1, Sets.complement (Sets.union state.s_token (S.InvownedToken s1)))
      (s2, Sets.complement (Sets.union state.s_token (S.InvownedToken s2))) ->
    state.s_STS s2

def Closed_transition {S : STS}
    (transition : STS_state_transition S) : Prop :=
  forall s1 s2 token1 token2 token3,
    transition (s1, token1) (s2, token2) ->
    Sets.equiv (Sets.intersect token1 token3) Sets.empty ->
    Sets.equiv (Sets.intersect token3 (S.InvownedToken s1)) Sets.empty ->
    transition (s1, Sets.union token1 token3) (s2, Sets.union token2 token3)

private theorem complement_token_join {S : STS}
    (owned frame inv : TokenSet S)
    (hOwnedInv : Sets.equiv (Sets.intersect owned inv) Sets.empty)
    (hFrameInv : Sets.equiv (Sets.intersect frame inv) Sets.empty) :
    TokenSet_join
      (Sets.complement (Sets.union (Sets.union owned frame) inv)) inv
      (Sets.complement (Sets.union owned frame)) := by
  constructor
  · intro token
    constructor
    · intro hOutside
      by_cases hInv : inv token
      · exact Or.inr hInv
      · exact Or.inl fun hAny => hAny.elim hOutside hInv
    · intro hJoined hOwnedOrFrame
      rcases hJoined with hOutside | hInv
      · exact hOutside (Or.inl hOwnedOrFrame)
      · rcases hOwnedOrFrame with hOwned | hFrame
        · exact ((hOwnedInv token).mp ⟨hOwned, hInv⟩).elim
        · exact ((hFrameInv token).mp ⟨hFrame, hInv⟩).elim
  · intro token
    constructor
    · intro hbad
      exact hbad.1 (Or.inr hbad.2)
    · intro hfalse
      exact hfalse.elim

private theorem token_join_frame_facts {S : STS}
    (owned frame inv base : TokenSet S)
    (hOwnedFrame : Sets.equiv (Sets.intersect owned frame) Sets.empty)
    (hjoin : TokenSet_join base inv
      (Sets.complement (Sets.union owned frame))) :
    Sets.equiv (Sets.union base frame)
        (Sets.complement (Sets.union owned inv)) ∧
      Sets.equiv (Sets.intersect base frame) Sets.empty ∧
      Sets.equiv (Sets.intersect frame inv) Sets.empty := by
  rcases hjoin with ⟨hcover, hInvBase⟩
  constructor
  · intro token
    constructor
    · intro hBaseOrFrame
      intro hOwnedOrInv
      rcases hBaseOrFrame with hBase | hFrame
      · rcases hOwnedOrInv with hOwned | hInv
        · exact (hcover token).mpr (Or.inl hBase) (Or.inl hOwned)
        · exact ((hInvBase token).mp ⟨hBase, hInv⟩).elim
      · rcases hOwnedOrInv with hOwned | hInv
        · exact ((hOwnedFrame token).mp ⟨hOwned, hFrame⟩).elim
        · exact (hcover token).mpr (Or.inr hInv) (Or.inr hFrame)
    · intro hOutside
      by_cases hFrame : frame token
      · exact Or.inr hFrame
      · have hWhole : Sets.complement (Sets.union owned frame) token :=
          fun h => h.elim (fun hOwned => hOutside (Or.inl hOwned)) hFrame
        rcases (hcover token).mp hWhole with hBase | hInv
        · exact Or.inl hBase
        · exact (hOutside (Or.inr hInv)).elim
  · constructor
    · intro token
      constructor
      · intro hbad
        exact (hcover token).mpr (Or.inl hbad.1) (Or.inr hbad.2)
      · intro hfalse
        exact hfalse.elim
    · intro token
      constructor
      · intro hbad
        exact (hcover token).mpr (Or.inr hbad.2) (Or.inr hbad.1)
      · intro hfalse
        exact hfalse.elim

theorem keep_rely_closed {S : STS} (ls1 ls2 ls3 : Lstate S)
    (hjoin : state_join ls1 ls2 ls3)
    (hvalid1 : valid_Lstate ls1)
    (hvalid2 : valid_Lstate ls2)
    (hrely1 : rely_closed ls1 S.Transition)
    (hrely2 : rely_closed ls2 S.Transition)
    (_hdisjoint : transtion_disjoint_preserved S.Transition)
    (hpreserved : transition_token_preserved S.Transition)
    (hclosed : Closed_transition S.Transition) :
    rely_closed ls3 S.Transition := by
  rcases hjoin with ⟨_, htokenJoin, hstateJoin⟩
  rcases htokenJoin with ⟨htokenEq, htokenDisjoint⟩
  intro before after hstateBefore htransition
  have hstatesBefore := (hstateJoin before).mp hstateBefore
  have hvalid1Before := hvalid1 before hstatesBefore.1
  have hvalid2Before := hvalid2 before hstatesBefore.2
  have hls3Token : ls3.s_token = Sets.union ls1.s_token ls2.s_token :=
    pred_ext1 _ _ _ htokenEq
  rw [hls3Token] at htransition
  apply (hstateJoin after).mpr
  constructor
  · let inputBase : TokenSet S :=
      Sets.complement
        (Sets.union (Sets.union ls1.s_token ls2.s_token) (S.InvownedToken before))
    let outputBase : TokenSet S :=
      Sets.complement
        (Sets.union (Sets.union ls1.s_token ls2.s_token) (S.InvownedToken after))
    let commonFrame : TokenSet S :=
      Sets.complement (Sets.union ls1.s_token ls2.s_token)
    have hjoinBefore : TokenSet_join inputBase (S.InvownedToken before) commonFrame :=
      complement_token_join ls1.s_token ls2.s_token (S.InvownedToken before)
        hvalid1Before hvalid2Before
    have hjoinAfter : TokenSet_join outputBase (S.InvownedToken after) commonFrame :=
      (hpreserved before after inputBase outputBase commonFrame htransition).mp hjoinBefore
    have hinputFacts :=
      token_join_frame_facts ls1.s_token ls2.s_token (S.InvownedToken before)
        inputBase htokenDisjoint hjoinBefore
    have houtputFacts :=
      token_join_frame_facts ls1.s_token ls2.s_token (S.InvownedToken after)
        outputBase htokenDisjoint hjoinAfter
    have hframed := hclosed before after inputBase outputBase ls2.s_token
      htransition hinputFacts.2.1 hinputFacts.2.2
    have hinputEq : Sets.union inputBase ls2.s_token =
        Sets.complement (Sets.union ls1.s_token (S.InvownedToken before)) :=
      pred_ext1 _ _ _ hinputFacts.1
    have houtputEq : Sets.union outputBase ls2.s_token =
        Sets.complement (Sets.union ls1.s_token (S.InvownedToken after)) :=
      pred_ext1 _ _ _ houtputFacts.1
    rw [hinputEq, houtputEq] at hframed
    exact hrely1 before after hstatesBefore.1 hframed
  · have hcomm : Sets.union ls2.s_token ls1.s_token =
        Sets.union ls1.s_token ls2.s_token :=
      pred_ext1 _ _ _ (Sets_union_comm ls2.s_token ls1.s_token)
    let inputBase : TokenSet S :=
      Sets.complement
        (Sets.union (Sets.union ls2.s_token ls1.s_token) (S.InvownedToken before))
    let outputBase : TokenSet S :=
      Sets.complement
        (Sets.union (Sets.union ls2.s_token ls1.s_token) (S.InvownedToken after))
    let commonFrame : TokenSet S :=
      Sets.complement (Sets.union ls2.s_token ls1.s_token)
    have htokenDisjoint' :
        Sets.equiv (Sets.intersect ls2.s_token ls1.s_token) Sets.empty :=
      Sets_equiv_trans (Sets_intersect_comm ls2.s_token ls1.s_token)
        htokenDisjoint
    have hjoinBefore : TokenSet_join inputBase (S.InvownedToken before) commonFrame :=
      complement_token_join ls2.s_token ls1.s_token (S.InvownedToken before)
        hvalid2Before hvalid1Before
    have htransition' : S.Transition (before, inputBase) (after, outputBase) := by
      simpa [inputBase, outputBase, hcomm] using htransition
    have hjoinAfter : TokenSet_join outputBase (S.InvownedToken after) commonFrame :=
      (hpreserved before after inputBase outputBase commonFrame htransition').mp hjoinBefore
    have hinputFacts :=
      token_join_frame_facts ls2.s_token ls1.s_token (S.InvownedToken before)
        inputBase htokenDisjoint' hjoinBefore
    have houtputFacts :=
      token_join_frame_facts ls2.s_token ls1.s_token (S.InvownedToken after)
        outputBase htokenDisjoint' hjoinAfter
    have hframed := hclosed before after inputBase outputBase ls1.s_token
      htransition' hinputFacts.2.1 hinputFacts.2.2
    have hinputEq : Sets.union inputBase ls1.s_token =
        Sets.complement (Sets.union ls2.s_token (S.InvownedToken before)) :=
      pred_ext1 _ _ _ hinputFacts.1
    have houtputEq : Sets.union outputBase ls1.s_token =
        Sets.complement (Sets.union ls2.s_token (S.InvownedToken after)) :=
      pred_ext1 _ _ _ houtputFacts.1
    rw [hinputEq, houtputEq] at hframed
    exact hrely2 before after hstatesBefore.2 hframed

def state_empty {S : STS} (state : Lstate S) : Prop :=
  mem_empty state.s_mem ∧
    Sets.equiv state.s_token Sets.empty ∧
    Sets.equiv state.s_STS Sets.full

def empty_state {S : STS} : Lstate S where
  s_mem := empty_mem
  s_STS := Sets.full
  s_token := Sets.empty

theorem empty_state_is_empty {S : STS} : state_empty (empty_state : Lstate S) := by
  exact ⟨empty_mem_empty, Sets_equiv_refl _, Sets_equiv_refl _⟩

structure STS_def : Type 1 where
  sts : STS

namespace CSLImpl

def Names (spec : STS_def) : LanguageSig.{0} where
  model := Lstate spec.sts
  join := state_join
  is_unit := state_empty

def DerivedNames (spec : STS_def) : DerivedNamesSig (Names spec) := {}

def PrimitiveRules (spec : STS_def) :
    PrimitiveRuleSig (Names spec) (DerivedNames spec) where
  unit_join := by
    intro state
    refine ⟨empty_state, empty_state_is_empty, ?_⟩
    exact ⟨mem_join_emp2 state.s_mem,
      ⟨Sets_equiv_symm (Sets_union_empty state.s_token),
        Sets_intersect_empty state.s_token⟩,
      Sets_equiv_symm (Sets_intersect_full state.s_STS)⟩
  unit_spec := by
    intro state result unit hunit hjoin
    rcases hunit with ⟨hunitMem, hunitToken, hunitStates⟩
    rcases hjoin with ⟨hjoinMem, ⟨hresultToken, _⟩, hresultStates⟩
    have hunitMem' := mem_empty_IS_empty_mem' unit.s_mem hunitMem
    have hmem : state.s_mem = result.s_mem := by
      rw [hunitMem'] at hjoinMem
      exact (mem_join_emp_r state.s_mem result.s_mem hjoinMem).symm
    apply Lstate_eq_split state result hmem
    · intro stsState
      have hu := hunitStates stsState
      have hr := hresultStates stsState
      constructor
      · intro hs
        exact hr.mpr ⟨hs, hu.mpr trivial⟩
      · intro hs
        exact (hr.mp hs).1
    · intro token
      have hu := hunitToken token
      have hr := hresultToken token
      constructor
      · intro ht
        exact hr.mpr (Or.inl ht)
      · intro ht
        rcases hr.mp ht with ht | hunit
        · exact ht
        · exact (hu.mp hunit).elim
  join_comm := by
    intro left right result hjoin
    rcases hjoin with ⟨hmem, ⟨htokenEq, htokenDisjoint⟩, hstateEq⟩
    exact ⟨mem_join_comm hmem,
      ⟨Sets_equiv_trans htokenEq (Sets_union_comm left.s_token right.s_token),
        Sets_equiv_trans (Sets_intersect_comm right.s_token left.s_token)
          htokenDisjoint⟩,
      Sets_equiv_trans hstateEq (Sets_intersect_comm left.s_STS right.s_STS)⟩
  join_assoc := by
    intro left middle right leftMiddle result hjoinLM hjoinResult
    rcases hjoinLM with ⟨hmemLM, ⟨htokenLM, htokenDisjointLM⟩, hstateLM⟩
    rcases hjoinResult with
      ⟨hmemResult, ⟨htokenResult, htokenDisjointResult⟩, hstateResult⟩
    let middleRight : Lstate spec.sts := {
      s_mem := merge middle.s_mem right.s_mem
      s_STS := Sets.intersect middle.s_STS right.s_STS
      s_token := Sets.union middle.s_token right.s_token }
    refine ⟨middleRight, ?_, ?_⟩
    · refine ⟨?_, ?_, Sets_equiv_refl _⟩
      · apply disjoint_merge_mem_join
        have hdisjointLeftMiddleRight := mem_join_disjoint hmemResult
        have hdisjointRightLeftMiddle := disjoint_comm hdisjointLeftMiddleRight
        exact disjoint_comm (disjoint_mem_join_r hdisjointRightLeftMiddle hmemLM)
      · constructor
        · exact Sets_equiv_refl _
        · intro token
          constructor
          · intro hbad
            have hMiddleInCombined := (htokenLM token).mpr (Or.inr hbad.1)
            exact ((htokenDisjointResult token).mp ⟨hMiddleInCombined, hbad.2⟩).elim
          · intro hfalse
            exact hfalse.elim
    · refine ⟨?_, ?_, ?_⟩
      · have hleftMiddleEq : leftMiddle.s_mem = merge left.s_mem middle.s_mem :=
          mem_join_eqmerge hmemLM
        rw [hleftMiddleEq] at hmemResult
        exact mem_join_merge_assoc_l (mem_join_disjoint hmemLM) hmemResult
      · constructor
        · intro token
          constructor
          · intro hResult
            rcases (htokenResult token).mp hResult with hLM | hRight
            · rcases (htokenLM token).mp hLM with hLeft | hMiddle
              · exact Or.inl hLeft
              · exact Or.inr (Or.inl hMiddle)
            · exact Or.inr (Or.inr hRight)
          · intro hCombined
            rcases hCombined with hLeft | hMiddle | hRight
            · exact (htokenResult token).mpr <| Or.inl <| (htokenLM token).mpr <| Or.inl hLeft
            · exact (htokenResult token).mpr <| Or.inl <| (htokenLM token).mpr <| Or.inr hMiddle
            · exact (htokenResult token).mpr <| Or.inr hRight
        · intro token
          constructor
          · intro hbad
            rcases hbad.2 with hMiddle | hRight
            · exact ((htokenDisjointLM token).mp ⟨hbad.1, hMiddle⟩).elim
            · have hLeftInCombined := (htokenLM token).mpr (Or.inl hbad.1)
              exact ((htokenDisjointResult token).mp ⟨hLeftInCombined, hRight⟩).elim
          · intro hfalse
            exact hfalse.elim
      · intro stsState
        constructor
        · intro hResult
          have hLMRight := (hstateResult stsState).mp hResult
          have hLeftMiddle := (hstateLM stsState).mp hLMRight.1
          exact ⟨hLeftMiddle.1, hLeftMiddle.2, hLMRight.2⟩
        · intro hAll
          exact (hstateResult stsState).mpr
            ⟨(hstateLM stsState).mpr ⟨hAll.1, hAll.2.1⟩, hAll.2.2⟩

def Context (spec : STS_def) : Facade.Context.{0, 0} where
  Names := Names spec
  DerivedNames := DerivedNames spec
  Rules := PrimitiveRules spec

def mstore (spec : STS_def) (p : addr) (value : Int) : (Context spec).expr :=
  fun state => exists stored,
    Byte.eqm value stored ∧
      state.s_mem = single_byte_mem p stored ∧
      Sets.equiv state.s_STS Sets.full ∧
      Sets.equiv state.s_token Sets.empty

def mstore_noninit (spec : STS_def) (p : addr) : (Context spec).expr :=
  fun state =>
    Sets.equiv state.s_STS Sets.full ∧
      Sets.equiv state.s_token Sets.empty ∧
      (state.s_mem = single_Noninit_mem p ∨
        exists value, state.s_mem = single_byte_mem p value)

theorem mstore_mstore_noninit (spec : STS_def)
    (p : addr) (value : Int) (state : Lstate spec.sts)
    (hstore : mstore spec p value state) : mstore_noninit spec p state := by
  rcases hstore with ⟨stored, _, hmem, hstates, htokens⟩
  exact ⟨hstates, htokens, Or.inr ⟨stored, hmem⟩⟩

theorem mstore_eqm (spec : STS_def) (p : addr) (value value' : Int)
    (heqm : Byte.eqm value value') :
    (Context spec).derivable1 (mstore spec p value) (mstore spec p value') := by
  intro state hstore
  rcases hstore with ⟨stored, hvalue, hrest⟩
  exact ⟨stored, Byte.eqm_trans _ _ _ (Byte.eqm_sym _ _ heqm) hvalue, hrest⟩

theorem dup_mstore_noninit (spec : STS_def) (p : addr) :
    (Context spec).derivable1
      ((Context spec).sepcon (mstore_noninit spec p) (mstore_noninit spec p))
      ((Context spec).coq_prop False) := by
  intro state hsep
  rcases hsep with ⟨left, right, hjoin, hleft, hright⟩
  have hmemJoin := hjoin.1
  have hrightNonempty : right.s_mem p ≠ Noperm := by
    rcases hright.2.2 with hrightMem | ⟨rightValue, hrightMem⟩
    · rw [hrightMem]
      simp [single_Noninit_mem, addr_eqb]
    · rw [hrightMem]
      simp [single_byte_mem, addr_eqb]
  rcases hleft.2.2 with hleftMem | ⟨leftValue, hleftMem⟩
  · have hat : left.s_mem p = Noninit := by
      rw [hleftMem]
      simp [single_Noninit_mem, addr_eqb]
    exact hrightNonempty
      (mem_join_Some1 left.s_mem right.s_mem state.s_mem p hmemJoin hat).1
  · have hat : left.s_mem p = value leftValue := by
      rw [hleftMem]
      simp [single_byte_mem, addr_eqb]
    exact hrightNonempty
      (mem_join_Some3 left.s_mem right.s_mem state.s_mem p leftValue hmemJoin hat).1

def at_states (spec : STS_def) (states : spec.sts.STS_state -> Prop) :
    (Context spec).expr :=
  fun state =>
    state.s_mem = empty_mem ∧
      Sets.equiv states state.s_STS ∧
      Sets.equiv state.s_token Sets.empty

def has_tokens (spec : STS_def) (tokens : TokenSet spec.sts) :
    (Context spec).expr :=
  fun state =>
    state.s_mem = empty_mem ∧
      Sets.equiv state.s_STS Sets.empty ∧
      Sets.equiv tokens state.s_token

def SeparationLogic (spec : STS_def) : SeparationLogicSig where
  toContext := Context spec
  mstore := mstore spec
  mstore_noninit := mstore_noninit spec
  mstore_mstore_noninit := mstore_mstore_noninit spec
  mstore_eqm := mstore_eqm spec
  dup_mstore_noninit := dup_mstore_noninit spec

end CSLImpl

structure CSL (_spec : STS_def) : Type 1 where
  mk ::

def CSL.canonical (spec : STS_def) : CSL spec := .mk

abbrev CSL.toSeparationLogicSig {spec : STS_def} (_logic : CSL spec) :
    SeparationLogicSig := CSLImpl.SeparationLogic spec

abbrev CSL.toContext {spec : STS_def} (_logic : CSL spec) := CSLImpl.Context spec
abbrev CSL.model {spec : STS_def} (logic : CSL spec) := logic.toContext.model
abbrev CSL.expr {spec : STS_def} (logic : CSL spec) := logic.toContext.expr
abbrev CSL.join {spec : STS_def} (logic : CSL spec) := logic.toContext.join
abbrev CSL.is_unit {spec : STS_def} (logic : CSL spec) := logic.toContext.is_unit
abbrev CSL.sepcon {spec : STS_def} (logic : CSL spec) := logic.toContext.sepcon
abbrev CSL.wand {spec : STS_def} (logic : CSL spec) := logic.toContext.wand
abbrev CSL.orp {spec : STS_def} (logic : CSL spec) := logic.toContext.orp
abbrev CSL.andp {spec : STS_def} (logic : CSL spec) := logic.toContext.andp
abbrev CSL.impp {spec : STS_def} (logic : CSL spec) := logic.toContext.impp
abbrev CSL.exp {spec : STS_def} (logic : CSL spec) := logic.toContext.exp
abbrev CSL.allp {spec : STS_def} (logic : CSL spec) := logic.toContext.allp
abbrev CSL.emp {spec : STS_def} (logic : CSL spec) := logic.toContext.emp
abbrev CSL.coq_prop {spec : STS_def} (logic : CSL spec) := logic.toContext.coq_prop
abbrev CSL.truep {spec : STS_def} (logic : CSL spec) := logic.toContext.truep
abbrev CSL.derivable1 {spec : STS_def} (logic : CSL spec) := logic.toContext.derivable1
abbrev CSL.logic_equiv {spec : STS_def} (logic : CSL spec) := logic.toContext.logic_equiv

abbrev CSL.mstore {spec : STS_def} (_logic : CSL spec) := CSLImpl.mstore spec
abbrev CSL.mstore_noninit {spec : STS_def} (_logic : CSL spec) :=
  CSLImpl.mstore_noninit spec
abbrev CSL.mstore_mstore_noninit {spec : STS_def} (_logic : CSL spec) :=
  CSLImpl.mstore_mstore_noninit spec
abbrev CSL.mstore_eqm {spec : STS_def} (_logic : CSL spec) :=
  CSLImpl.mstore_eqm spec
abbrev CSL.dup_mstore_noninit {spec : STS_def} (_logic : CSL spec) :=
  CSLImpl.dup_mstore_noninit spec
abbrev CSL.at_states {spec : STS_def} (_logic : CSL spec) := CSLImpl.at_states spec
abbrev CSL.has_tokens {spec : STS_def} (_logic : CSL spec) := CSLImpl.has_tokens spec

def naive_S : STS where
  token := PEmpty
  STS_state := PEmpty
  Transition := fun _ _ => False
  InvownedToken := fun _ _ => False

def STS_naive : STS_def := ⟨naive_S⟩

end SimpleC.SL.ConAssertion
