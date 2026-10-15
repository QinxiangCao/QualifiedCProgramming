import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 600
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P040_1983C_have_your_cake_and_eat_it_too_goal P040_1983C_have_your_cake_and_eat_it_too_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev matrix := naive_C_Rules.Int64PtrArray2

private theorem row_length (a b c : List Int) (who : Int) (hw : 0≤who ∧ who<3)
    (hb : Zlength b=Zlength a) (hc : Zlength c=Zlength a) : Zlength (Znth who [a,b,c] [])=Zlength a := by
  rcases show who=0 ∨ who=1 ∨ who=2 by omega with rfl|rfl|rfl <;> first | exact hb | exact hc | rfl

private theorem need_bounds (a b c : List Int) (need : Int) (hp : Pre a b c)
    (hn : need=Z.quot (sum a+2) 3) : 1≤need ∧ need≤200000000000 := by
  have hh := cake_sum_bounds_from_forall__try_initialization a hp.2.2.2.1
  change Zlength a≤sum a ∧ sum a≤Zlength a*1000000 at hh
  have hl := hp.1
  have hdiv : Z.quot (sum a+2) 3=(sum a+2)/3 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  rw [hdiv] at hn
  omega

private theorem quot_div (a : List Int) (need : Int) (ha : 0≤CakeSum a)
    (hn : need=Z.quot (sum a+2) 3) : need=Z.div (CakeSum a+2) 3 := by
  have he : Z.quot (CakeSum a+2) 3=Z.div (CakeSum a+2) 3 := (Int.fdiv_eq_tdiv_of_nonneg (by omega) (by omega)).symm
  exact hn.trans he

private theorem order_index (ord : List Int) (k : Int) (ho : CakeOrder ord) (hk : 0≤k ∧ k<3) : 0≤Znth k ord 0 ∧ Znth k ord 0<3 := by
  rcases show k=0 ∨ k=1 ∨ k=2 by omega with rfl|rfl|rfl <;>
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

private theorem sum_snoc (row : List Int) (start i : Int) (hs : 0≤start ∧ start≤i) (hi : i<Zlength row) :
    CakeSum (sublist start (i+1) row)=CakeSum (sublist start i row)+Znth i row 0 := by
  have hx := suffix_sum_extend__try_terminal_semantics [row] 0 start i (CakeSum (sublist start i row)) ⟨hs.1,hs.2,by change i≤Zlength row; omega,rfl⟩ hi
  exact hx.2.2.2.symm

private theorem merge_row (a b c : List Int) (v who row_ptr n : Int) (hw : 0≤who ∧ who<3)
    (hn : n=Zlength (Znth who [a,b,c] [])) :
    (matrix.missing_i v 3 who row_ptr [a,b,c] ** ((v+who*sizeof(PTR)) # Ptr |-> row_ptr) **
      int64Array.full row_ptr n (Znth who [a,b,c] [])) |-- matrix.full v 3 [a,b,c] := by
  have hm := matrix.missing_i_merge_to_full v who 3 row_ptr [a,b,c] (Znth who [a,b,c] []) hw
  rw [replace_Znth_Znth] at hm
  change ((((v+who*sizeof(PTR)) # Ptr |-> row_ptr) ** int64Array.full row_ptr (Zlength (Znth who [a,b,c] [])) (Znth who [a,b,c] [])) ** matrix.missing_i v 3 who row_ptr [a,b,c]) |-- matrix.full v 3 [a,b,c] at hm
  rw [hn]
  apply naive_C_Rules.toContext.derivable1_trans _ _ _ ?_ hm
  cancel

private theorem split_row (a b c : List Int) (v who n : Int) (hw : 0≤who ∧ who<3)
    (hn : n=Zlength (Znth who [a,b,c] [])) :
    matrix.full v 3 [a,b,c] |-- EX row_ptr : Int,
      matrix.missing_i v 3 who row_ptr [a,b,c] ** ((v+who*sizeof(PTR)) # Ptr |-> row_ptr) **
      int64Array.full row_ptr n (Znth who [a,b,c] []) := by
  have hm := matrix.full_split_to_missing_i v who 3 [a,b,c] hw
  change matrix.full v 3 [a,b,c] |-- EX row_ptr : Int, ((((v+who*sizeof(PTR)) # Ptr |-> row_ptr) ** int64Array.full row_ptr (Zlength (Znth who [a,b,c] [])) (Znth who [a,b,c] [])) ** matrix.missing_i v 3 who row_ptr [a,b,c]) at hm
  sep_apply hm
  Intros row_ptr
  refine Automation.exp_right_rule (CRules := naive_C_Rules) row_ptr ?_
  rw [hn]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> assumption

private theorem triple0 {A : Type} (a b c d : A) : Znth 0 [a,b,c] d=a := rfl
private theorem triple1 {A : Type} (a b c d : A) : Znth 1 [a,b,c] d=b := rfl
private theorem triple2 {A : Type} (a b c d : A) : Znth 2 [a,b,c] d=c := rfl

private theorem output_left (left right : List Int) (i : Int) (hi : 0≤i ∧ i<3) :
    Znth (2*i) (OutputBounds left right) 0+1=Znth i left 0 := by
  rcases show i=0 ∨ i=1 ∨ i=2 by omega with rfl|rfl|rfl
  · change Znth 0 left 0-1+1=Znth 0 left 0; omega
  · change Znth 1 left 0-1+1=Znth 1 left 0; omega
  · change Znth 2 left 0-1+1=Znth 2 left 0; omega

private theorem output_right (left right : List Int) (i : Int) (hi : 0≤i ∧ i<3) :
    Znth (2*i+1) (OutputBounds left right) 0+1=Znth i right 0 := by
  rcases show i=0 ∨ i=1 ∨ i=2 by omega with rfl|rfl|rfl
  · change Znth 0 right 0-1+1=Znth 0 right 0; omega
  · change Znth 1 right 0-1+1=Znth 1 right 0; omega
  · change Znth 2 right 0-1+1=Znth 2 right 0; omega

private theorem merge_orders (ptr z : Int) (before after : List Int) (hz : 0≤z ∧ z<6) :
    (intArray.full (ptr+3*z*sizeof(INT)) 3 (OrderFor z) **
      intArray.seg ptr 0 (3*z) before ** intArray.seg ptr (3*(z+1)) 18 after) |--
      intArray.full ptr 18 (before++OrderFor z++after) := by
  sep_apply (intArray.full_to_seg (ptr+3*z*sizeof(INT)) 3 (OrderFor z))
  have hs := (intArray.seg_shift ptr (3*z) 0 3 (OrderFor z)).right
  change intArray.seg (ptr+3*z*sizeof(INT)) 0 3 (OrderFor z) |-- intArray.seg ptr (3*z+0) (3*z+3) (OrderFor z) at hs
  rw [Int.add_zero,show 3*z+3=3*(z+1) by omega] at hs
  sep_apply hs
  sep_apply (intArray.seg_merge_to_seg ptr 0 (3*z) (3*(z+1)) before (OrderFor z) (by omega))
  sep_apply (intArray.seg_merge_to_full ptr 0 (3*(z+1)) 18 (before++OrderFor z) after (by omega))
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero,List.append_assoc]
  cancel

theorem proof_of_try_order_safety_wit_11_split_goal_1 : try_order_safety_wit_11_split_goal_1 := by
  unfold try_order_safety_wit_11_split_goal_1
  intro out_pre order_pre need_pre n_pre v_pre ord c b a row_ptr lefts rights acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dump_pre_spatial
  have hv := PreH7 who pos ⟨⟨by omega,by omega⟩,by omega⟩
  omega

theorem proof_of_try_order_safety_wit_11_split_goal_2 : try_order_safety_wit_11_split_goal_2 := by
  unfold try_order_safety_wit_11_split_goal_2
  intro out_pre order_pre need_pre n_pre v_pre ord c b a row_ptr lefts rights acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dump_pre_spatial
  have hv := PreH7 who pos ⟨⟨by omega,by omega⟩,by omega⟩
  omega

theorem proof_of_try_order_safety_wit_11 : try_order_safety_wit_11 := by
  unfold try_order_safety_wit_11
  right
  intro out_pre order_pre need_pre n_pre v_pre ord c b a row_ptr lefts rights acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pures
  · exact proof_of_try_order_safety_wit_11_split_goal_1 out_pre order_pre need_pre n_pre v_pre ord c b a row_ptr lefts rights acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  · exact proof_of_try_order_safety_wit_11_split_goal_2 out_pre order_pre need_pre n_pre v_pre ord c b a row_ptr lefts rights acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27

theorem proof_of_try_order_safety_wit_20_split_goal_1 : try_order_safety_wit_20_split_goal_1 := by
  unfold try_order_safety_wit_20_split_goal_1
  intro out_pre order_pre need_pre n_pre v_pre ord c b a row_ptr lefts rights acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  dump_pre_spatial
  have hv := PreH6 who i ⟨⟨by omega,by omega⟩,by omega⟩
  omega

theorem proof_of_try_order_safety_wit_20_split_goal_2 : try_order_safety_wit_20_split_goal_2 := by
  unfold try_order_safety_wit_20_split_goal_2
  intro out_pre order_pre need_pre n_pre v_pre ord c b a row_ptr lefts rights acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  dump_pre_spatial
  have hv := PreH6 who i ⟨⟨by omega,by omega⟩,by omega⟩
  omega

theorem proof_of_try_order_safety_wit_20 : try_order_safety_wit_20 := by
  unfold try_order_safety_wit_20
  right
  intro out_pre order_pre need_pre n_pre v_pre ord c b a row_ptr lefts rights acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pures
  · exact proof_of_try_order_safety_wit_20_split_goal_1 out_pre order_pre need_pre n_pre v_pre ord c b a row_ptr lefts rights acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  · exact proof_of_try_order_safety_wit_20_split_goal_2 out_pre order_pre need_pre n_pre v_pre ord c b a row_ptr lefts rights acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23

theorem proof_of_try_order_entail_wit_1_split_goal_1 : try_order_entail_wit_1_split_goal_1 := by
  unfold try_order_entail_wit_1_split_goal_1
  intro need_pre n_pre ord c b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  refine ⟨PreH9,rfl,rfl,⟨by omega,by omega⟩,⟨by omega,?_⟩,?_,rfl⟩
  · change 0≤Zlength a; omega
  · intro k hk; omega

theorem proof_of_try_order_entail_wit_1_split_goal_2 : try_order_entail_wit_1_split_goal_2 := by
  unfold try_order_entail_wit_1_split_goal_2
  intro need_pre n_pre ord c b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact (need_bounds a b c need_pre PreH6 PreH8).2

theorem proof_of_try_order_entail_wit_1_split_goal_3 : try_order_entail_wit_1_split_goal_3 := by
  unfold try_order_entail_wit_1_split_goal_3
  intro need_pre n_pre ord c b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact (need_bounds a b c need_pre PreH6 PreH8).1

theorem proof_of_try_order_entail_wit_1 : try_order_entail_wit_1 := by
  unfold try_order_entail_wit_1
  right
  intro need_pre n_pre ord c b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact (proof_of_try_order_entail_wit_1_split_goal_1 need_pre n_pre ord c b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_1_split_goal_1 need_pre n_pre ord c b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
      | exact (proof_of_try_order_entail_wit_1_split_goal_2 need_pre n_pre ord c b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_1_split_goal_2 need_pre n_pre ord c b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
      | exact (proof_of_try_order_entail_wit_1_split_goal_3 need_pre n_pre ord c b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_1_split_goal_3 need_pre n_pre ord c b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))

theorem proof_of_try_order_entail_wit_2 : try_order_entail_wit_2 := by
  unfold try_order_entail_wit_2
  right
  intro need_pre n_pre v_pre ord c b a pos lefts_2 rights_2 part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hw := order_index ord part PreH12 ⟨by omega,by omega⟩
  have hl := row_length a b c (Znth part ord 0) hw PreH4 PreH5
  have hp := PreH16.2.2.2.2.1
  change 0≤pos ∧ pos≤Zlength a at hp
  sep_apply (split_row a b c v_pre (Znth part ord 0) n_pre hw (by omega))
  Intros row_ptr
  refine Automation.exp_right_rule (CRules := naive_C_Rules) row_ptr ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | rfl | omega | tauto

theorem proof_of_try_order_entail_wit_3_split_goal_1 : try_order_entail_wit_3_split_goal_1 := by
  unfold try_order_entail_wit_3_split_goal_1
  intro need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hpos := PreH20.2.2.2.2.1
  change 0≤pos ∧ pos≤Zlength a at hpos
  have hstart : 0≤start ∧ start≤Zlength a := by omega
  have hl := row_length a b c who ⟨by omega,by omega⟩ (by omega) (by omega)
  refine ⟨hstart.1,le_refl _,by omega,?_,?_⟩
  · rw [Zsublist_nil _ start start (le_refl _)]; rfl
  · intro q hq; omega

theorem proof_of_try_order_entail_wit_3_split_goal_2 : try_order_entail_wit_3_split_goal_2 := by
  unfold try_order_entail_wit_3_split_goal_2
  intro need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hpos := PreH20.2.2.2.2.1
  change 0≤pos ∧ pos≤Zlength a at hpos
  have hstart : 0≤start ∧ start≤Zlength a := by omega
  omega

theorem proof_of_try_order_entail_wit_3_split_goal_3 : try_order_entail_wit_3_split_goal_3 := by
  unfold try_order_entail_wit_3_split_goal_3
  intro need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hpos := PreH20.2.2.2.2.1
  change 0≤pos ∧ pos≤Zlength a at hpos
  have hstart : 0≤start ∧ start≤Zlength a := by omega
  omega

theorem proof_of_try_order_entail_wit_3_split_goal_4 : try_order_entail_wit_3_split_goal_4 := by
  unfold try_order_entail_wit_3_split_goal_4
  intro need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hpos := PreH20.2.2.2.2.1
  change 0≤pos ∧ pos≤Zlength a at hpos
  have hstart : 0≤start ∧ start≤Zlength a := by omega
  omega

theorem proof_of_try_order_entail_wit_3_split_goal_5 : try_order_entail_wit_3_split_goal_5 := by
  unfold try_order_entail_wit_3_split_goal_5
  intro need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hpos := PreH20.2.2.2.2.1
  change 0≤pos ∧ pos≤Zlength a at hpos
  have hstart : 0≤start ∧ start≤Zlength a := by omega
  omega

theorem proof_of_try_order_entail_wit_3 : try_order_entail_wit_3 := by
  unfold try_order_entail_wit_3
  right
  intro need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact (proof_of_try_order_entail_wit_3_split_goal_1 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_3_split_goal_1 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
      | exact (proof_of_try_order_entail_wit_3_split_goal_2 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_3_split_goal_2 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
      | exact (proof_of_try_order_entail_wit_3_split_goal_3 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_3_split_goal_3 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
      | exact (proof_of_try_order_entail_wit_3_split_goal_4 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_3_split_goal_4 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))
      | exact (proof_of_try_order_entail_wit_3_split_goal_5 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_3_split_goal_5 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))

theorem proof_of_try_order_entail_wit_4_split_goal_1 : try_order_entail_wit_4_split_goal_1 := by
  unfold try_order_entail_wit_4_split_goal_1
  intro need_pre n_pre ord c b a lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hl := row_length a b c who ⟨by omega,by omega⟩ (by omega) (by omega)
  rcases PreH27 with ⟨hs,hsp,hpn,ha,hm⟩
  refine ⟨hs,by omega,by omega,?_,?_⟩
  · rw [sum_snoc _ start pos ⟨hs,hsp⟩ (by omega),ha]
  · intro q hq
    by_cases hqpos:q<pos
    · exact hm q ⟨hq.1,hqpos⟩
    · have he : q=pos := by omega
      rw [he,← ha]
      omega

theorem proof_of_try_order_entail_wit_4_split_goal_2 : try_order_entail_wit_4_split_goal_2 := by
  unfold try_order_entail_wit_4_split_goal_2
  intro need_pre n_pre ord c b a lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hh := need_bounds a b c need_pre PreH8 PreH10
  have hv := PreH7 who pos ⟨⟨by omega,by omega⟩,by omega⟩
  have hs := PreH27.2.2.2.1
  have hlo := PreH27.1
  have hr := PreH27.2.1
  have hl := row_length a b c who ⟨by omega,by omega⟩ (by omega) (by omega)
  apply suffix_sum_upper__try_terminal_semantics [a,b,c] who start pos acc ⟨hlo,hr,PreH27.2.2.1,hs⟩ (by omega)
  · intro k hk
    have hv := PreH7 who k ⟨⟨by omega,by omega⟩,by omega⟩
    omega
  · omega

theorem proof_of_try_order_entail_wit_4_split_goal_3 : try_order_entail_wit_4_split_goal_3 := by
  unfold try_order_entail_wit_4_split_goal_3
  intro need_pre n_pre ord c b a lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hv := PreH7 who pos ⟨⟨by omega,by omega⟩,by omega⟩
  omega

theorem proof_of_try_order_entail_wit_4 : try_order_entail_wit_4 := by
  unfold try_order_entail_wit_4
  right
  intro need_pre n_pre ord c b a lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact (proof_of_try_order_entail_wit_4_split_goal_1 need_pre n_pre ord c b a lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_4_split_goal_1 need_pre n_pre ord c b a lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
      | exact (proof_of_try_order_entail_wit_4_split_goal_2 need_pre n_pre ord c b a lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_4_split_goal_2 need_pre n_pre ord c b a lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
      | exact (proof_of_try_order_entail_wit_4_split_goal_3 need_pre n_pre ord c b a lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_4_split_goal_3 need_pre n_pre ord c b a lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))

theorem proof_of_try_order_entail_wit_5_1_split_goal_1 : try_order_entail_wit_5_1_split_goal_1 := by
  unfold try_order_entail_wit_5_1_split_goal_1
  intro need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  dump_pre_spatial
  assumption

theorem proof_of_try_order_entail_wit_5_1_split_goal_spatial : try_order_entail_wit_5_1_split_goal_spatial := by
  unfold try_order_entail_wit_5_1_split_goal_spatial
  intro need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hl := row_length a b c who ⟨by omega,by omega⟩ (by omega) (by omega)
  exact merge_row a b c v_pre who row_ptr n_pre ⟨by omega,by omega⟩ (by omega)

theorem proof_of_try_order_entail_wit_5_1 : try_order_entail_wit_5_1 := by
  unfold try_order_entail_wit_5_1
  right
  intro need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pure_spatial
  · exact (proof_of_try_order_entail_wit_5_1_split_goal_spatial need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26)
  · split_pures
    all_goals first
      | exact (proof_of_try_order_entail_wit_5_1_split_goal_1 need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_5_1_split_goal_1 need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26))

theorem proof_of_try_order_entail_wit_5_2_split_goal_1 : try_order_entail_wit_5_2_split_goal_1 := by
  unfold try_order_entail_wit_5_2_split_goal_1
  intro need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dump_pre_spatial
  exact PreH27.2.1

theorem proof_of_try_order_entail_wit_5_2_split_goal_2 : try_order_entail_wit_5_2_split_goal_2 := by
  unfold try_order_entail_wit_5_2_split_goal_2
  intro need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  dump_pre_spatial
  assumption

theorem proof_of_try_order_entail_wit_5_2_split_goal_spatial : try_order_entail_wit_5_2_split_goal_spatial := by
  unfold try_order_entail_wit_5_2_split_goal_spatial
  intro need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hl := row_length a b c who ⟨by omega,by omega⟩ (by omega) (by omega)
  exact merge_row a b c v_pre who row_ptr n_pre ⟨by omega,by omega⟩ (by omega)

theorem proof_of_try_order_entail_wit_5_2 : try_order_entail_wit_5_2 := by
  unfold try_order_entail_wit_5_2
  right
  intro need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · exact (proof_of_try_order_entail_wit_5_2_split_goal_spatial need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
  · split_pures
    all_goals first
      | exact (proof_of_try_order_entail_wit_5_2_split_goal_1 need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_5_2_split_goal_1 need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
      | exact (proof_of_try_order_entail_wit_5_2_split_goal_2 need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_5_2_split_goal_2 need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc pos start who part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))

theorem proof_of_try_order_entail_wit_6_split_goal_1 : try_order_entail_wit_6_split_goal_1 := by
  unfold try_order_entail_wit_6_split_goal_1
  intro need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hn := need_bounds a b c need_pre PreH7 PreH9
  have htot := cake_sum_bounds_from_forall__try_initialization a PreH7.2.2.2.1
  have ht : 0≤CakeSum a := by omega
  have hd := quot_div a need_pre ht PreH9
  have hposn : pos=n_pre := by have h:=PreH20 PreH1; omega
  rw [hposn] at PreH22
  rcases PreH21 with ⟨ho,hll,hrl,hpart,hpos,hdone,hstart⟩
  rcases PreH22 with ⟨hs0,hsp,hpn,ha,hmin⟩
  intro bounds hb hord
  rcases hb with ⟨la,ra,lb,rb,lc,rc,total,hbeq,htotal,hla,hra,hlb,hrb,hlc,hrc,hdab,hdac,hdbc,hva,hvb,hvc⟩
  subst bounds
  subst total
  have hva' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need_pre (CakeSum (sublist la (ra+1) a)) ht hd).mpr hva
  have hvb' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need_pre (CakeSum (sublist lb (rb+1) b)) ht hd).mpr hvb
  have hvc' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need_pre (CakeSum (sublist lc (rc+1) c)) ht hd).mpr hvc
  have hna : ∀k,(0≤k ∧ k<Zlength a) → 0≤Znth k a 0 := by
    intro k hk
    have hh := PreH6 0 k ⟨⟨by omega,by omega⟩,by omega⟩
    change 1≤Znth k a 0 ∧ Znth k a 0≤1000000 at hh
    omega
  have hnb : ∀k,(0≤k ∧ k<Zlength b) → 0≤Znth k b 0 := by
    intro k hk
    have hh := PreH6 1 k ⟨⟨by omega,by omega⟩,by omega⟩
    change 1≤Znth k b 0 ∧ Znth k b 0≤1000000 at hh
    omega
  have hnc : ∀k,(0≤k ∧ k<Zlength c) → 0≤Znth k c 0 := by
    intro k hk
    have hh := PreH6 2 k ⟨⟨by omega,by omega⟩,by omega⟩
    change 1≤Znth k c 0 ∧ Znth k c 0≤1000000 at hh
    omega
  rcases ho with rfl|rfl|rfl|rfl|rfl|rfl
  · rcases show part=0 ∨ part=1 by omega with he|he
    · subst part
      change who=0 at PreH14
      subst who
      change start=0 at hstart
      rw [hstart] at ha
      change acc=CakeSum (sublist 0 n_pre a) at ha
      have hi := sum_sublist_inclusion__try_terminal_semantics a 0 la (ra+1) n_pre hna ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
      omega
    · subst part
      change who=1 at PreH14
      subst who
      change start=Znth 0 rights_2 0 at hstart
      rw [hstart] at ha
      change acc=CakeSum (sublist (Znth 0 rights_2 0) n_pre b) at ha
      have hf := hdone 0 (by omega)
      norm_num only [triple0,triple1,triple2] at hf
      rcases hf with ⟨_,hfl,hfr,hfn,hfs,hfv,hfm⟩
      simp only [ite_true] at hfs
      have hlo : Znth 0 lefts_2 0-1=0 := by omega
      rw [hlo] at hfm
      have ho12 := hord.2.1
      change ra<lb at ho12
      have hcut : Znth 0 rights_2 0≤ra+1 := by
        by_contra hnot
        have hm := hfm (ra+1) ⟨by omega,by omega⟩
        have hi := sum_sublist_inclusion__try_terminal_semantics a 0 la (ra+1) (ra+1) hna ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
        omega
      have hi := sum_sublist_inclusion__try_terminal_semantics b (Znth 0 rights_2 0) lb (rb+1) n_pre hnb ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
      omega
  · rcases show part=0 ∨ part=1 by omega with he|he
    · subst part
      change who=0 at PreH14
      subst who
      change start=0 at hstart
      rw [hstart] at ha
      change acc=CakeSum (sublist 0 n_pre a) at ha
      have hi := sum_sublist_inclusion__try_terminal_semantics a 0 la (ra+1) n_pre hna ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
      omega
    · subst part
      change who=2 at PreH14
      subst who
      change start=Znth 0 rights_2 0 at hstart
      rw [hstart] at ha
      change acc=CakeSum (sublist (Znth 0 rights_2 0) n_pre c) at ha
      have hf := hdone 0 (by omega)
      norm_num only [triple0,triple1,triple2] at hf
      rcases hf with ⟨_,hfl,hfr,hfn,hfs,hfv,hfm⟩
      simp only [ite_true] at hfs
      have hlo : Znth 0 lefts_2 0-1=0 := by omega
      rw [hlo] at hfm
      have ho12 := hord.2.1
      change ra<lc at ho12
      have hcut : Znth 0 rights_2 0≤ra+1 := by
        by_contra hnot
        have hm := hfm (ra+1) ⟨by omega,by omega⟩
        have hi := sum_sublist_inclusion__try_terminal_semantics a 0 la (ra+1) (ra+1) hna ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
        omega
      have hi := sum_sublist_inclusion__try_terminal_semantics c (Znth 0 rights_2 0) lc (rc+1) n_pre hnc ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
      omega
  · rcases show part=0 ∨ part=1 by omega with he|he
    · subst part
      change who=1 at PreH14
      subst who
      change start=0 at hstart
      rw [hstart] at ha
      change acc=CakeSum (sublist 0 n_pre b) at ha
      have hi := sum_sublist_inclusion__try_terminal_semantics b 0 lb (rb+1) n_pre hnb ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
      omega
    · subst part
      change who=0 at PreH14
      subst who
      change start=Znth 1 rights_2 0 at hstart
      rw [hstart] at ha
      change acc=CakeSum (sublist (Znth 1 rights_2 0) n_pre a) at ha
      have hf := hdone 0 (by omega)
      norm_num only [triple0,triple1,triple2] at hf
      rcases hf with ⟨_,hfl,hfr,hfn,hfs,hfv,hfm⟩
      simp only [ite_true] at hfs
      have hlo : Znth 1 lefts_2 0-1=0 := by omega
      rw [hlo] at hfm
      have ho12 := hord.2.1
      change rb<la at ho12
      have hcut : Znth 1 rights_2 0≤rb+1 := by
        by_contra hnot
        have hm := hfm (rb+1) ⟨by omega,by omega⟩
        have hi := sum_sublist_inclusion__try_terminal_semantics b 0 lb (rb+1) (rb+1) hnb ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
        omega
      have hi := sum_sublist_inclusion__try_terminal_semantics a (Znth 1 rights_2 0) la (ra+1) n_pre hna ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
      omega
  · rcases show part=0 ∨ part=1 by omega with he|he
    · subst part
      change who=1 at PreH14
      subst who
      change start=0 at hstart
      rw [hstart] at ha
      change acc=CakeSum (sublist 0 n_pre b) at ha
      have hi := sum_sublist_inclusion__try_terminal_semantics b 0 lb (rb+1) n_pre hnb ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
      omega
    · subst part
      change who=2 at PreH14
      subst who
      change start=Znth 1 rights_2 0 at hstart
      rw [hstart] at ha
      change acc=CakeSum (sublist (Znth 1 rights_2 0) n_pre c) at ha
      have hf := hdone 0 (by omega)
      norm_num only [triple0,triple1,triple2] at hf
      rcases hf with ⟨_,hfl,hfr,hfn,hfs,hfv,hfm⟩
      simp only [ite_true] at hfs
      have hlo : Znth 1 lefts_2 0-1=0 := by omega
      rw [hlo] at hfm
      have ho12 := hord.2.1
      change rb<lc at ho12
      have hcut : Znth 1 rights_2 0≤rb+1 := by
        by_contra hnot
        have hm := hfm (rb+1) ⟨by omega,by omega⟩
        have hi := sum_sublist_inclusion__try_terminal_semantics b 0 lb (rb+1) (rb+1) hnb ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
        omega
      have hi := sum_sublist_inclusion__try_terminal_semantics c (Znth 1 rights_2 0) lc (rc+1) n_pre hnc ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
      omega
  · rcases show part=0 ∨ part=1 by omega with he|he
    · subst part
      change who=2 at PreH14
      subst who
      change start=0 at hstart
      rw [hstart] at ha
      change acc=CakeSum (sublist 0 n_pre c) at ha
      have hi := sum_sublist_inclusion__try_terminal_semantics c 0 lc (rc+1) n_pre hnc ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
      omega
    · subst part
      change who=0 at PreH14
      subst who
      change start=Znth 2 rights_2 0 at hstart
      rw [hstart] at ha
      change acc=CakeSum (sublist (Znth 2 rights_2 0) n_pre a) at ha
      have hf := hdone 0 (by omega)
      norm_num only [triple0,triple1,triple2] at hf
      rcases hf with ⟨_,hfl,hfr,hfn,hfs,hfv,hfm⟩
      simp only [ite_true] at hfs
      have hlo : Znth 2 lefts_2 0-1=0 := by omega
      rw [hlo] at hfm
      have ho12 := hord.2.1
      change rc<la at ho12
      have hcut : Znth 2 rights_2 0≤rc+1 := by
        by_contra hnot
        have hm := hfm (rc+1) ⟨by omega,by omega⟩
        have hi := sum_sublist_inclusion__try_terminal_semantics c 0 lc (rc+1) (rc+1) hnc ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
        omega
      have hi := sum_sublist_inclusion__try_terminal_semantics a (Znth 2 rights_2 0) la (ra+1) n_pre hna ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
      omega
  · rcases show part=0 ∨ part=1 by omega with he|he
    · subst part
      change who=2 at PreH14
      subst who
      change start=0 at hstart
      rw [hstart] at ha
      change acc=CakeSum (sublist 0 n_pre c) at ha
      have hi := sum_sublist_inclusion__try_terminal_semantics c 0 lc (rc+1) n_pre hnc ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
      omega
    · subst part
      change who=1 at PreH14
      subst who
      change start=Znth 2 rights_2 0 at hstart
      rw [hstart] at ha
      change acc=CakeSum (sublist (Znth 2 rights_2 0) n_pre b) at ha
      have hf := hdone 0 (by omega)
      norm_num only [triple0,triple1,triple2] at hf
      rcases hf with ⟨_,hfl,hfr,hfn,hfs,hfv,hfm⟩
      simp only [ite_true] at hfs
      have hlo : Znth 2 lefts_2 0-1=0 := by omega
      rw [hlo] at hfm
      have ho12 := hord.2.1
      change rc<lb at ho12
      have hcut : Znth 2 rights_2 0≤rc+1 := by
        by_contra hnot
        have hm := hfm (rc+1) ⟨by omega,by omega⟩
        have hi := sum_sublist_inclusion__try_terminal_semantics c 0 lc (rc+1) (rc+1) hnc ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
        omega
      have hi := sum_sublist_inclusion__try_terminal_semantics b (Znth 2 rights_2 0) lb (rb+1) n_pre hnb ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
      omega

theorem proof_of_try_order_entail_wit_6_split_goal_2 : try_order_entail_wit_6_split_goal_2 := by
  unfold try_order_entail_wit_6_split_goal_2
  intro need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hl := row_length a b c who ⟨by omega,by omega⟩ (by omega) (by omega)
  rcases PreH22 with ⟨hs,hsp,hpn,ha,hm⟩
  have hx := sum_sublist_nonnegative__try_terminal_semantics (Znth who [a,b,c] []) start pos
    (fun k hk=>by have h:=PreH6 who k ⟨⟨by omega,by omega⟩,by omega⟩; omega) ⟨hs,hsp⟩ hpn
  omega

theorem proof_of_try_order_entail_wit_6 : try_order_entail_wit_6 := by
  unfold try_order_entail_wit_6
  right
  intro need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact (proof_of_try_order_entail_wit_6_split_goal_1 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_6_split_goal_1 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))
      | exact (proof_of_try_order_entail_wit_6_split_goal_2 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_6_split_goal_2 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))

theorem proof_of_try_order_entail_wit_7_split_goal_1 : try_order_entail_wit_7_split_goal_1 := by
  unfold try_order_entail_wit_7_split_goal_1
  intro need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hn := need_bounds a b c need_pre PreH7 PreH9
  have hl := row_length a b c who ⟨PreH15,PreH16⟩ PreH4 PreH5
  rcases PreH21 with ⟨ho,hll,hrl,hpart,hpos,hdone,hstart⟩
  rcases PreH22 with ⟨hs0,hsp,hpn,ha,hmin⟩
  have hslt : start<pos := by
    by_contra hnot
    have he : start=pos := by omega
    rw [he,Zsublist_nil _ pos pos (le_refl _)] at ha
    change acc=0 at ha
    omega
  have hprev := order_index ord 0 ho (by omega)
  have hdifferent : Znth 0 ord 0≠Znth 1 ord 0 := by
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  refine ⟨ho,?_,?_,⟨by omega,by omega⟩,⟨by omega,?_⟩,?_,?_⟩
  · rw [Zlength_replace_Znth]; exact hll
  · rw [Zlength_replace_Znth]; exact hrl
  · change pos≤Zlength a; omega
  · intro k hk
    dsimp only
    by_cases hkp:k=part
    · subst k
      rw [← PreH14,Znth_replace_Znth_Same 0 lefts_2 who _ ⟨PreH15,by omega⟩,
        Znth_replace_Znth_Same 0 rights_2 who _ ⟨PreH15,by omega⟩]
      refine ⟨⟨PreH15,PreH16⟩,by omega,by omega,hpn,?_,?_,?_⟩
      · rcases show part=0 ∨ part=1 by omega with he|he
        · subst part
          simp only [ite_true] at hstart ⊢
          omega
        · subst part
          have hne : who≠Znth 0 ord 0 := by rw [PreH14]; exact Ne.symm hdifferent
          norm_num only at hstart ⊢
          simp only [ite_false] at hstart ⊢
          rw [Znth_replace_Znth_Diff 0 rights_2 who (Znth 0 ord 0) pos ⟨PreH15,by omega⟩ ⟨hprev.1,by omega⟩ hne]
          omega
      · rw [Int.add_sub_cancel,← ha]
        exact PreH1
      · intro q hq
        rw [Int.add_sub_cancel] at hq ⊢
        exact hmin q hq
    · have he : part=1 := by omega
      have hk0 : k=0 := by omega
      subst part
      subst k
      have hne : who≠Znth 0 ord 0 := by rw [PreH14]; exact Ne.symm hdifferent
      have hdone0 := hdone 0 (by omega)
      rw [Znth_replace_Znth_Diff 0 lefts_2 who (Znth 0 ord 0) _ ⟨PreH15,by omega⟩ ⟨hprev.1,by omega⟩ hne,
        Znth_replace_Znth_Diff 0 rights_2 who (Znth 0 ord 0) _ ⟨PreH15,by omega⟩ ⟨hprev.1,by omega⟩ hne]
      simpa only [ite_true] using hdone0
  · rw [if_neg (show part+1≠0 by omega),Int.add_sub_cancel,← PreH14,Znth_replace_Znth_Same 0 rights_2 who pos ⟨PreH15,by omega⟩]

theorem proof_of_try_order_entail_wit_7_split_goal_2 : try_order_entail_wit_7_split_goal_2 := by
  unfold try_order_entail_wit_7_split_goal_2
  intro need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact (need_bounds a b c need_pre PreH7 PreH9).2

theorem proof_of_try_order_entail_wit_7_split_goal_3 : try_order_entail_wit_7_split_goal_3 := by
  unfold try_order_entail_wit_7_split_goal_3
  intro need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  exact (need_bounds a b c need_pre PreH7 PreH9).1

theorem proof_of_try_order_entail_wit_7 : try_order_entail_wit_7 := by
  unfold try_order_entail_wit_7
  right
  intro need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact (proof_of_try_order_entail_wit_7_split_goal_1 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_7_split_goal_1 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))
      | exact (proof_of_try_order_entail_wit_7_split_goal_2 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_7_split_goal_2 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))
      | exact (proof_of_try_order_entail_wit_7_split_goal_3 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_7_split_goal_3 need_pre n_pre ord c b a lefts_2 rights_2 part who start pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))

theorem proof_of_try_order_entail_wit_8 : try_order_entail_wit_8 := by
  unfold try_order_entail_wit_8
  right
  intro need_pre n_pre v_pre ord c b a pos lefts_2 rights_2 part PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have he : part=2 := by omega
  rw [he] at PreH16
  have hw := order_index ord 2 PreH12 ⟨by omega,by omega⟩
  have hl := row_length a b c (Znth 2 ord 0) hw PreH4 PreH5
  have hp := PreH16.2.2.2.2.1
  change 0≤pos ∧ pos≤Zlength a at hp
  sep_apply (split_row a b c v_pre (Znth 2 ord 0) n_pre hw (by omega))
  Intros row_ptr
  refine Automation.exp_right_rule (CRules := naive_C_Rules) row_ptr ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | rfl | omega | tauto

theorem proof_of_try_order_entail_wit_9_split_goal_1 : try_order_entail_wit_9_split_goal_1 := by
  unfold try_order_entail_wit_9_split_goal_1
  intro need_pre n_pre ord c b a lefts_2 rights_2 who pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hl := selected_row_length__try_terminal_semantics a b c ord who PreH11 PreH13 (by omega) (by omega)
  exact suffix_sum_empty__try_terminal_semantics [a,b,c] who pos (by omega) (by omega)

theorem proof_of_try_order_entail_wit_9 : try_order_entail_wit_9 := by
  unfold try_order_entail_wit_9
  right
  intro need_pre n_pre ord c b a lefts_2 rights_2 who pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact (proof_of_try_order_entail_wit_9_split_goal_1 need_pre n_pre ord c b a lefts_2 rights_2 who pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_9_split_goal_1 need_pre n_pre ord c b a lefts_2 rights_2 who pos acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))

theorem proof_of_try_order_entail_wit_10_split_goal_1 : try_order_entail_wit_10_split_goal_1 := by
  unfold try_order_entail_wit_10_split_goal_1
  intro need_pre n_pre ord c b a lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hl := selected_row_length__try_terminal_semantics a b c ord who PreH12 PreH14 (by omega) (by omega)
  exact suffix_sum_extend__try_terminal_semantics [a,b,c] who pos i acc PreH23 (by omega)

theorem proof_of_try_order_entail_wit_10_split_goal_2 : try_order_entail_wit_10_split_goal_2 := by
  unfold try_order_entail_wit_10_split_goal_2
  intro need_pre n_pre ord c b a lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hl := selected_row_length__try_terminal_semantics a b c ord who PreH12 PreH14 (by omega) (by omega)
  apply suffix_sum_upper__try_terminal_semantics [a,b,c] who pos i acc PreH23 (by omega)
  · intro k hk
    have h := PreH6 who k ⟨⟨by omega,by omega⟩,by omega⟩
    omega
  · omega

theorem proof_of_try_order_entail_wit_10_split_goal_3 : try_order_entail_wit_10_split_goal_3 := by
  unfold try_order_entail_wit_10_split_goal_3
  intro need_pre n_pre ord c b a lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hv := PreH6 who i ⟨⟨by omega,by omega⟩,by omega⟩
  omega

theorem proof_of_try_order_entail_wit_10 : try_order_entail_wit_10 := by
  unfold try_order_entail_wit_10
  right
  intro need_pre n_pre ord c b a lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact (proof_of_try_order_entail_wit_10_split_goal_1 need_pre n_pre ord c b a lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_10_split_goal_1 need_pre n_pre ord c b a lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
      | exact (proof_of_try_order_entail_wit_10_split_goal_2 need_pre n_pre ord c b a lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_10_split_goal_2 need_pre n_pre ord c b a lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
      | exact (proof_of_try_order_entail_wit_10_split_goal_3 need_pre n_pre ord c b a lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_10_split_goal_3 need_pre n_pre ord c b a lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))

theorem proof_of_try_order_entail_wit_11_split_goal_1 : try_order_entail_wit_11_split_goal_1 := by
  unfold try_order_entail_wit_11_split_goal_1
  intro need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  dump_pre_spatial
  have he : i=n_pre := by omega
  rw [← he]
  exact PreH23

theorem proof_of_try_order_entail_wit_11_split_goal_2 : try_order_entail_wit_11_split_goal_2 := by
  unfold try_order_entail_wit_11_split_goal_2
  intro need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  dump_pre_spatial
  assumption

theorem proof_of_try_order_entail_wit_11_split_goal_spatial : try_order_entail_wit_11_split_goal_spatial := by
  unfold try_order_entail_wit_11_split_goal_spatial
  intro need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hl := row_length a b c who ⟨by omega,by omega⟩ (by omega) (by omega)
  exact merge_row a b c v_pre who row_ptr n_pre ⟨by omega,by omega⟩ (by omega)

theorem proof_of_try_order_entail_wit_11 : try_order_entail_wit_11 := by
  unfold try_order_entail_wit_11
  right
  intro need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pure_spatial
  · exact (proof_of_try_order_entail_wit_11_split_goal_spatial need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
  · split_pures
    all_goals first
      | exact (proof_of_try_order_entail_wit_11_split_goal_1 need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_11_split_goal_1 need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))
      | exact (proof_of_try_order_entail_wit_11_split_goal_2 need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_11_split_goal_2 need_pre n_pre v_pre ord c b a row_ptr lefts_2 rights_2 acc i pos who PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23))

theorem proof_of_try_order_entail_wit_12_split_goal_1 : try_order_entail_wit_12_split_goal_1 := by
  unfold try_order_entail_wit_12_split_goal_1
  intro need_pre n_pre ord c b a lefts_2 rights_2 pos who acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hh := cake_sum_bounds_from_forall__try_initialization a PreH7.2.2.2.1
  have hd := quot_div a need_pre (by omega) PreH9
  have ht := greedy_terminal_try_order__try_terminal_semantics a b c ord need_pre n_pre pos who acc lefts_2 rights_2 PreH7 PreH6 PreH8 hd PreH12 PreH16 PreH21 PreH22
  exact ht.1 PreH1

theorem proof_of_try_order_entail_wit_12 : try_order_entail_wit_12 := by
  unfold try_order_entail_wit_12
  right
  intro need_pre n_pre ord c b a lefts_2 rights_2 pos who acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact (proof_of_try_order_entail_wit_12_split_goal_1 need_pre n_pre ord c b a lefts_2 rights_2 pos who acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_12_split_goal_1 need_pre n_pre ord c b a lefts_2 rights_2 pos who acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))

theorem proof_of_try_order_entail_wit_13_split_goal_1 : try_order_entail_wit_13_split_goal_1 := by
  unfold try_order_entail_wit_13_split_goal_1
  intro need_pre n_pre ord c b a lefts_2 rights_2 pos who acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hh := cake_sum_bounds_from_forall__try_initialization a PreH7.2.2.2.1
  have hd := quot_div a need_pre (by omega) PreH9
  have ht := greedy_terminal_try_order__try_terminal_semantics a b c ord need_pre n_pre pos who acc lefts_2 rights_2 PreH7 PreH6 PreH8 hd PreH12 PreH16 PreH21 PreH22
  exact ht.2 (by omega)

theorem proof_of_try_order_entail_wit_13 : try_order_entail_wit_13 := by
  unfold try_order_entail_wit_13
  right
  intro need_pre n_pre ord c b a lefts_2 rights_2 pos who acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact (proof_of_try_order_entail_wit_13_split_goal_1 need_pre n_pre ord c b a lefts_2 rights_2 pos who acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_13_split_goal_1 need_pre n_pre ord c b a lefts_2 rights_2 pos who acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))

theorem proof_of_try_order_entail_wit_14 : try_order_entail_wit_14 := by
  unfold try_order_entail_wit_14
  right
  intro out_pre need_pre n_pre v_pre ord c b a lefts_2 rights_2 pos who acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ([] : List Int) ?_
  sep_apply (intArray.undef_full_to_undef_seg out_pre 6)
  split_pure_spatial
  · simp only [Int.mul_zero]
    have he : emp |-- intArray.seg out_pre 0 0 [] := by
      intro s hs
      exact ⟨rfl,rfl,hs⟩
    have hf : ((matrix.full v_pre 3 [a,b,c] ** emp) ** intArray.undef_seg out_pre 0 6) |-- ((matrix.full v_pre 3 [a,b,c] ** intArray.seg out_pre 0 0 []) ** intArray.undef_seg out_pre 0 6) :=
      naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _
        (naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _ (naive_C_Rules.toContext.derivable1_refl _) he)
        (naive_C_Rules.toContext.derivable1_refl _)
    apply naive_C_Rules.toContext.derivable1_trans _ _ _ ?_ hf
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | (intro j hj; omega)

theorem proof_of_try_order_entail_wit_15 : try_order_entail_wit_15 := by
  unfold try_order_entail_wit_15
  right
  intro out_pre need_pre n_pre v_pre ord c b a lefts_2 rights_2 raw_prefix_2 i acc who pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hl1 : Zlength (raw_prefix_2++[Znth i lefts_2 0])=2*i+1 := by
    rw [Zlength_app,PreH10]; rfl
  have hl2 : Zlength ((raw_prefix_2++[Znth i lefts_2 0])++[Znth i rights_2 0])=2*(i+1) := by
    rw [Zlength_app,hl1]; change 2*i+1+1=2*(i+1); omega
  have hnew : ∀j,(0≤j ∧ j<2*(i+1)) → Znth j ((raw_prefix_2++[Znth i lefts_2 0])++[Znth i rights_2 0]) 0=Znth j (OutputBounds lefts_2 rights_2) 0+1 := by
    intro j hj
    by_cases hold : j<2*i
    · rw [Znth_app_left__try_output_materialization _ _ 0 j (by omega),
        Znth_app_left__try_output_materialization _ _ 0 j (by omega)]
      exact PreH12 j ⟨hj.1,hold⟩
    · rcases show j=2*i ∨ j=2*i+1 by omega with he|he
      · subst j
        rw [Znth_app_left__try_output_materialization _ _ 0 (2*i) (by omega)]
        rw [←PreH10,Znth_app_last__try_output_materialization]
        rw [PreH10,output_left _ _ i ⟨PreH8,PreH1⟩]
      · subst j
        rw [←hl1,Znth_app_last__try_output_materialization]
        rw [hl1,output_right _ _ i ⟨PreH8,PreH1⟩]
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ((raw_prefix_2++[Znth i lefts_2 0])++[Znth i rights_2 0]) ?_
  rw [show 2*i+1+1=2*(i+1) by omega]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega

theorem proof_of_try_order_entail_wit_16_split_goal_1 : try_order_entail_wit_16_split_goal_1 := by
  unfold try_order_entail_wit_16_split_goal_1
  intro need_pre n_pre ord c b a lefts_2 rights_2 raw_prefix i acc who pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  intro j hj
  apply PreH12 j
  omega

theorem proof_of_try_order_entail_wit_16 : try_order_entail_wit_16 := by
  unfold try_order_entail_wit_16
  right
  intro need_pre n_pre ord c b a lefts_2 rights_2 raw_prefix i acc who pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact (proof_of_try_order_entail_wit_16_split_goal_1 need_pre n_pre ord c b a lefts_2 rights_2 raw_prefix i acc who pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12)
      | (dump_pre_spatial; exact (proof_of_try_order_entail_wit_16_split_goal_1 need_pre n_pre ord c b a lefts_2 rights_2 raw_prefix i acc who pos PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12))

theorem proof_of_try_order_return_wit_1 : try_order_return_wit_1 := by
  unfold try_order_return_wit_1
  right
  intro need_pre n_pre ord c b a lefts rights raw_result_2 pos who acc PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (OutputBounds lefts rights) ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> assumption

theorem proof_of_solver_safety_wit_23_split_goal_1 : solver_safety_wit_23_split_goal_1 := by
  unfold solver_safety_wit_23_split_goal_1
  intro out_pre n_pre v_pre c b a row0_addr total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  dump_pre_spatial
  have hv := PreH6 0 i ⟨⟨by omega,by omega⟩,by omega⟩
  change 1≤Znth i a 0 ∧ Znth i a 0≤1000000 at hv
  omega

theorem proof_of_solver_safety_wit_23_split_goal_2 : solver_safety_wit_23_split_goal_2 := by
  unfold solver_safety_wit_23_split_goal_2
  intro out_pre n_pre v_pre c b a row0_addr total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  dump_pre_spatial
  have hv := PreH6 0 i ⟨⟨by omega,by omega⟩,by omega⟩
  change 1≤Znth i a 0 ∧ Znth i a 0≤1000000 at hv
  omega

theorem proof_of_solver_safety_wit_23 : solver_safety_wit_23 := by
  unfold solver_safety_wit_23
  right
  intro out_pre n_pre v_pre c b a row0_addr total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pures
  · exact proof_of_solver_safety_wit_23_split_goal_1 out_pre n_pre v_pre c b a row0_addr total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  · exact proof_of_solver_safety_wit_23_split_goal_2 out_pre n_pre v_pre c b a row0_addr total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro n_pre v_pre c b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  sep_apply (split_row a b c v_pre 0 n_pre (by omega) PreH7)
  Intros row0
  refine Automation.exp_right_rule (CRules := naive_C_Rules) row0 ?_
  split_pure_spatial
  · cancel
    exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial <;> first | assumption | rfl | omega

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  unfold solver_entail_wit_2_split_goal_1
  intro n_pre c b a total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  rw [Zsublist_nil a 0 0 (le_refl _)]
  rfl

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  right
  intro n_pre c b a total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact (proof_of_solver_entail_wit_2_split_goal_1 n_pre c b a total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8)
      | (dump_pre_spatial; exact (proof_of_solver_entail_wit_2_split_goal_1 n_pre c b a total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8))

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  unfold solver_entail_wit_3_split_goal_1
  intro n_pre c b a total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  apply suffix_sum_upper__try_terminal_semantics [a] 0 0 i total ⟨by omega,by omega,by change i≤Zlength a; omega,PreH11⟩ (by change i<Zlength a; omega)
  · intro k hk
    have h:=PreH6 0 k ⟨⟨by omega,by omega⟩,hk.2⟩
    change 0≤Znth k a 0 ∧ Znth k a 0≤1000000
    change 1≤Znth k a 0 ∧ Znth k a 0≤1000000 at h
    omega
  · change Zlength a≤200000; omega

theorem proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2 := by
  unfold solver_entail_wit_3_split_goal_2
  intro n_pre c b a total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have h:=PreH6 0 i ⟨⟨by omega,by omega⟩,by omega⟩
  change 1≤Znth i a 0 ∧ Znth i a 0≤1000000 at h
  omega

theorem proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3 := by
  unfold solver_entail_wit_3_split_goal_3
  intro n_pre c b a total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  change total+Znth i a 0=CakeSum (sublist 0 (i+1) a)
  rw [sum_snoc a 0 i ⟨by omega,by omega⟩ (by omega)]
  change total=sum (sublist 0 i a) at PreH11
  change total+_=sum (sublist 0 i a)+_
  rw [PreH11]

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  unfold solver_entail_wit_3
  right
  intro n_pre c b a total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact (proof_of_solver_entail_wit_3_split_goal_1 n_pre c b a total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
      | (dump_pre_spatial; exact (proof_of_solver_entail_wit_3_split_goal_1 n_pre c b a total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
      | exact (proof_of_solver_entail_wit_3_split_goal_2 n_pre c b a total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
      | (dump_pre_spatial; exact (proof_of_solver_entail_wit_3_split_goal_2 n_pre c b a total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
      | exact (proof_of_solver_entail_wit_3_split_goal_3 n_pre c b a total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
      | (dump_pre_spatial; exact (proof_of_solver_entail_wit_3_split_goal_3 n_pre c b a total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))

theorem proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1 := by
  unfold solver_entail_wit_4_split_goal_1
  intro n_pre v_pre c b a row0_addr total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  dump_pre_spatial
  have he:i=Zlength a := by omega
  rw [he,sublist_full__try_terminal_semantics] at PreH11
  exact PreH11

theorem proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2 := by
  unfold solver_entail_wit_4_split_goal_2
  intro n_pre v_pre c b a row0_addr total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  dump_pre_spatial
  assumption

theorem proof_of_solver_entail_wit_4_split_goal_spatial : solver_entail_wit_4_split_goal_spatial := by
  unfold solver_entail_wit_4_split_goal_spatial
  intro n_pre v_pre c b a row0_addr total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact merge_row a b c v_pre 0 row0_addr n_pre ⟨by omega,by omega⟩ PreH8

theorem proof_of_solver_entail_wit_4 : solver_entail_wit_4 := by
  unfold solver_entail_wit_4
  right
  intro n_pre v_pre c b a row0_addr total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · exact (proof_of_solver_entail_wit_4_split_goal_spatial n_pre v_pre c b a row0_addr total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
  · split_pures
    all_goals first
      | exact (proof_of_solver_entail_wit_4_split_goal_1 n_pre v_pre c b a row0_addr total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
      | (dump_pre_spatial; exact (proof_of_solver_entail_wit_4_split_goal_1 n_pre v_pre c b a row0_addr total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))
      | exact (proof_of_solver_entail_wit_4_split_goal_2 n_pre v_pre c b a row0_addr total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13)
      | (dump_pre_spatial; exact (proof_of_solver_entail_wit_4_split_goal_2 n_pre v_pre c b a row0_addr total i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13))

theorem proof_of_solver_entail_wit_5 : solver_entail_wit_5 := by
  unfold solver_entail_wit_5
  right
  intro n_pre c b a total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hn := need_bounds a b c (Z.quot (total+2) 3) PreH6 (by rw [PreH8])
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | (unfold FailedOrders; intro k hk; omega) | (rw [PreH8])

theorem proof_of_solver_entail_wit_6 : solver_entail_wit_6 := by
  unfold solver_entail_wit_6
  right
  intro n_pre v_pre c b a table_2 z need total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  rcases order_table_decomposition__solver_order_setup table_2 z PreH15 ⟨PreH13,PreH1⟩ with ⟨he,hb,ho,ha,hat,hcake,hm,hm2,ht⟩
  rw [List.append_assoc] at he
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (sublist 0 (3*z) table_2) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (sublist (3*(z+1)) 18 table_2) ?_
  split_pure_spatial
  · sep_apply (intArray.full_split_to_seg (&("orders")) (3*z) 18 table_2 (by omega))
    sep_apply (intArray.seg_split_to_seg (&("orders")) (3*z) (3*(z+1)) 18 (sublist (3*z) 18 table_2) (by omega))
    rw [hm2,ht]
    sep_apply (intArray.seg_to_full (&("orders")) (3*z) (3*(z+1)) (OrderFor z))
    rw [show 3*(z+1)-3*z=3 by omega]
    cancel
    exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | (rw [←he]; exact PreH15)

theorem proof_of_solver_entail_wit_9 : solver_entail_wit_9 := by
  unfold solver_entail_wit_9
  right
  intro n_pre v_pre c b a table_2 before_2 after_2 total need z ordp raw_result_2 result_2 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  refine Automation.exp_right_rule (CRules := naive_C_Rules) before_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) after_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) result_2 ?_
  split_pure_spatial
  · rw [PreH18]
    sep_apply (merge_orders (&("orders")) z before_2 after_2 ⟨PreH15,PreH16⟩)
    simp only [List.append_assoc]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | (exact Or.inl ⟨result_2,rfl,PreH2.1⟩) | (rw [←PreH20]; exact PreH19)

theorem proof_of_solver_entail_wit_10 : solver_entail_wit_10 := by
  unfold solver_entail_wit_10
  right
  intro n_pre v_pre c b a table_2 before after total need z ordp retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hf : FailedOrders a b c (z+1) := by
    intro k hk
    by_cases hlt:k<z
    · exact PreH16 k ⟨hk.1,hlt⟩
    · have he:k=z := by omega
      subst k
      exact ⟨OrderFor z,PreH23,PreH2⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) table_2 ?_
  split_pure_spatial
  · rw [PreH17,PreH19]
    sep_apply (merge_orders (&("orders")) z before after ⟨PreH14,PreH15⟩)
    simp only [List.append_assoc]
    cancel
  · split_pures <;> dump_pre_spatial <;> assumption

theorem proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1 := by
  unfold solver_entail_wit_11_split_goal_1
  intro n_pre c b a table_2 total need z ok ordp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  intro row col hr
  rcases show row=0 ∨ row=1 ∨ row=2 by omega with rfl|rfl|rfl
  · exact (Forall_Znth__solver_order_iteration _ 0 a).mp PreH5.2.2.2.1 col ⟨by omega,by omega⟩
  · exact (Forall_Znth__solver_order_iteration _ 0 b).mp PreH5.2.2.2.2.1 col ⟨by omega,by omega⟩
  · exact (Forall_Znth__solver_order_iteration _ 0 c).mp PreH5.2.2.2.2.2.1 col ⟨by omega,by omega⟩

theorem proof_of_solver_entail_wit_11 : solver_entail_wit_11 := by
  unfold solver_entail_wit_11
  right
  intro n_pre c b a table_2 total need z ok ordp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact (proof_of_solver_entail_wit_11_split_goal_1 n_pre c b a table_2 total need z ok ordp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
      | (dump_pre_spatial; exact (proof_of_solver_entail_wit_11_split_goal_1 n_pre c b a table_2 total need z ok ordp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))

theorem proof_of_solver_entail_wit_12_split_goal_1 : solver_entail_wit_12_split_goal_1 := by
  unfold solver_entail_wit_12_split_goal_1
  intro n_pre c b a table_2 z need total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have he:z=6 := by omega
  rw [he] at PreH16
  exact failed_six_orders_spec_none__solver_final_results a b c PreH16

theorem proof_of_solver_entail_wit_12_split_goal_2 : solver_entail_wit_12_split_goal_2 := by
  unfold solver_entail_wit_12_split_goal_2
  intro n_pre c b a table_2 z need total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have he:z=6 := by omega
  rw [he] at PreH16
  exact PreH16

theorem proof_of_solver_entail_wit_12 : solver_entail_wit_12 := by
  unfold solver_entail_wit_12
  right
  intro n_pre c b a table_2 z need total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | exact (proof_of_solver_entail_wit_12_split_goal_1 n_pre c b a table_2 z need total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
      | (dump_pre_spatial; exact (proof_of_solver_entail_wit_12_split_goal_1 n_pre c b a table_2 z need total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
      | exact (proof_of_solver_entail_wit_12_split_goal_2 n_pre c b a table_2 z need total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)
      | (dump_pre_spatial; exact (proof_of_solver_entail_wit_12_split_goal_2 n_pre c b a table_2 z need total PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  unfold solver_return_wit_2
  right
  intro c b a table before after result_2 raw_result_2 total need z ok ordp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  refine Automation.exp_right_rule (CRules := naive_C_Rules) result_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> assumption

theorem proof_of_solver_partial_solve_wit_2_pure_split_goal_1 : solver_partial_solve_wit_2_pure_split_goal_1 := by
  unfold solver_partial_solve_wit_2_pure_split_goal_1
  intro out_pre n_pre v_pre c b a table before after row0_addr total need z ordp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  dump_pre_spatial
  assumption

theorem proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure := by
  unfold solver_partial_solve_wit_2_pure
  right
  intro out_pre n_pre v_pre c b a table before after row0_addr total need z ordp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pures
  · exact proof_of_solver_partial_solve_wit_2_pure_split_goal_1 out_pre n_pre v_pre c b a table before after row0_addr total need z ordp PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too_proof_manual
