import SimpleC.SL.SeparationLogic

namespace FloatVCGoalTests

open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.DerivedPredSigCompat
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance : SacContext := ⟨naive_C_Rules⟩

inductive float_swap_para where
  | float_swap_eq_para : fp32 -> float_swap_para
  | float_swap_neq_para : fp32 -> fp32 -> float_swap_para

def float_swap_pre (px py : Int) : float_swap_para -> Assertion
  | .float_swap_eq_para x => “ px = py ” && px # Float |-> x
  | .float_swap_neq_para x y => px # Float |-> x ** py # Float |-> y

def float_swap_post (px py : Int) : float_swap_para -> Assertion
  | .float_swap_eq_para x => “ px = py ” && px # Float |-> x
  | .float_swap_neq_para x y => px # Float |-> y ** py # Float |-> x

inductive double_swap_para where
  | double_swap_eq_para : fp64 -> double_swap_para
  | double_swap_neq_para : fp64 -> fp64 -> double_swap_para

def double_swap_pre (px py : Int) : double_swap_para -> Assertion
  | .double_swap_eq_para x => “ px = py ” && px # Double |-> x
  | .double_swap_neq_para x y => px # Double |-> x ** py # Double |-> y

def double_swap_post (px py : Int) : double_swap_para -> Assertion
  | .double_swap_eq_para x => “ px = py ” && px # Double |-> x
  | .double_swap_neq_para x y => px # Double |-> y ** py # Double |-> x

def float_swap_entail_wit_1 : Prop :=
  forall (py_pre px_pre : Int) (para_all : float_swap_para),
    float_swap_pre px_pre py_pre para_all |--
      (EX y : fp32, EX x : fp32,
        “ para_all = .float_swap_neq_para x y ” &&
          px_pre # Float |-> x ** py_pre # Float |-> y) ||
      (EX x : fp32,
        “ px_pre = py_pre ” &&
        “ para_all = .float_swap_eq_para x ” &&
          px_pre # Float |-> x)

def float_swap_return_wit_1 : Prop :=
  forall (py_pre px_pre : Int) (para_all : float_swap_para)
      (x y : fp32) (_PreH1 : para_all = .float_swap_neq_para x y),
    px_pre # Float |-> y ** py_pre # Float |-> x |--
      float_swap_post px_pre py_pre para_all

def float_swap_return_wit_2 : Prop :=
  forall (py_pre px_pre : Int) (para_all : float_swap_para)
      (x : fp32) (_PreH1 : px_pre = py_pre)
      (_PreH2 : para_all = .float_swap_eq_para x),
    py_pre # Float |-> x |-- float_swap_post px_pre py_pre para_all

def double_swap_entail_wit_1 : Prop :=
  forall (py_pre px_pre : Int) (para_all : double_swap_para),
    double_swap_pre px_pre py_pre para_all |--
      (EX y : fp64, EX x : fp64,
        “ para_all = .double_swap_neq_para x y ” &&
          px_pre # Double |-> x ** py_pre # Double |-> y) ||
      (EX x : fp64,
        “ px_pre = py_pre ” &&
        “ para_all = .double_swap_eq_para x ” &&
          px_pre # Double |-> x)

def double_swap_return_wit_1 : Prop :=
  forall (py_pre px_pre : Int) (para_all : double_swap_para)
      (x y : fp64) (_PreH1 : para_all = .double_swap_neq_para x y),
    px_pre # Double |-> y ** py_pre # Double |-> x |--
      double_swap_post px_pre py_pre para_all

def double_swap_return_wit_2 : Prop :=
  forall (py_pre px_pre : Int) (para_all : double_swap_para)
      (x : fp64) (_PreH1 : px_pre = py_pre)
      (_PreH2 : para_all = .double_swap_eq_para x),
    py_pre # Double |-> x |-- double_swap_post px_pre py_pre para_all

def float_add_wit : Prop :=
  forall (px py pr : Int) (x y : fp32),
    px # Float |-> x ** py # Float |-> y ** pr # Float |-> fp32_add x y |--
      EX result : fp32,
        “ result = fp32_add x y ” &&
          px # Float |-> x ** py # Float |-> y ** pr # Float |-> result

def float_sub_wit : Prop :=
  forall (px py pr : Int) (x y : fp32),
    px # Float |-> x ** py # Float |-> y ** pr # Float |-> fp32_sub x y |--
      EX result : fp32,
        “ result = fp32_sub x y ” &&
          px # Float |-> x ** py # Float |-> y ** pr # Float |-> result

def double_add_wit : Prop :=
  forall (px py pr : Int) (x y : fp64),
    px # Double |-> x ** py # Double |-> y ** pr # Double |-> fp64_add x y |--
      EX result : fp64,
        “ result = fp64_add x y ” &&
          px # Double |-> x ** py # Double |-> y ** pr # Double |-> result

def double_sub_wit : Prop :=
  forall (px py pr : Int) (x y : fp64),
    px # Double |-> x ** py # Double |-> y ** pr # Double |-> fp64_sub x y |--
      EX result : fp64,
        “ result = fp64_sub x y ” &&
          px # Double |-> x ** py # Double |-> y ** pr # Double |-> result

end FloatVCGoalTests
