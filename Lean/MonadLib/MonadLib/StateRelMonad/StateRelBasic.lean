import MonadLib.Monad
import FP.SetsFixedpoints
import AUXLib.SetoidRewrite

namespace MonadLib.StateRelMonad

open AUXLib FP
open scoped SetsNotation MonadNotation

abbrev M (Sigma A : Type) : Type := Sigma -> A -> Sigma -> Prop

def bind {Sigma A B : Type} (f : M Sigma A) (g : A -> M Sigma B) : M Sigma B :=
  fun s1 b s3 => exists a s2, f s1 a s2 /\ g a s2 b s3

def ret {Sigma A : Type} (a0 : A) : M Sigma A :=
  fun s1 a s2 => a = a0 /\ s1 = s2

instance state_rel_monad (Sigma : Type) : Monad (M Sigma) where
  bind := bind
  ret := ret

abbrev program := M
abbrev MONAD (A : Type) := program Unit A

def test {Sigma : Type} (P : Sigma -> Prop) : program Sigma Unit :=
  fun s1 _ s2 => P s1 /\ s1 = s2

def test' {Sigma : Type} (P : Prop) : program Sigma Unit :=
  fun s1 _ s2 => P /\ s1 = s2

def choice {Sigma A : Type} (f g : program Sigma A) : program Sigma A :=
  fun s a s' => f s a s' \/ g s a s'

def any {Sigma : Type} (A : Type) : program Sigma A :=
  fun s1 _ s2 => s1 = s2

def get {Sigma A : Type} (P : Sigma -> A -> Prop) : program Sigma A :=
  fun s1 a s2 => P s1 a /\ s1 = s2

def get' {Sigma A : Type} (f : Sigma -> A) : program Sigma A :=
  get fun s a => a = f s

def update {Sigma : Type} (P : Sigma -> Sigma -> Prop) : program Sigma Unit :=
  fun s1 _ s2 => P s1 s2

def update' {Sigma : Type} (f : Sigma -> Sigma) : program Sigma Unit :=
  update fun s s' => s' = f s

def If {Sigma : Type} (cond : Sigma -> Prop) (c : program Sigma Unit) :
    program Sigma Unit :=
  choice (test cond ;; c) (test fun s => Not (cond s))

def if_else {Sigma A : Type} (cond : Sigma -> Prop)
    (c1 c2 : program Sigma A) : program Sigma A :=
  choice (test cond ;; c1) (test (fun s => Not (cond s)) ;; c2)

namespace StateRelMonadNotation

scoped notation "skip" => StateRelMonad.ret ()
scoped notation:50 "assume!! " P:50 => StateRelMonad.test' P
scoped notation:50 "assume " P:50 => StateRelMonad.test P

end StateRelMonadNotation

def while_f {Sigma : Type} (cond : program Sigma Bool) (body : program Sigma Unit)
    (W : program Sigma Unit) : program Sigma Unit :=
  x <- cond ;;
  match x with
  | true => body ;; W
  | false => ret ()

def «while» {Sigma : Type} (cond : program Sigma Bool) (body : program Sigma Unit) :
    program Sigma Unit :=
  Lfix (while_f cond body)

def whileret_f {Sigma A : Type} (cond : A -> program Sigma Bool)
    (body : A -> program Sigma A) (W : A -> program Sigma A) :
    A -> program Sigma A :=
  fun a =>
    x <- cond a ;;
    match x with
    | true => bind (body a) W
    | false => ret a

def whileret {Sigma A : Type} (cond : A -> program Sigma Bool)
    (body : A -> program Sigma A) : A -> program Sigma A :=
  Lfix (whileret_f cond body)

def whileP_f {Sigma : Type} (cond : Sigma -> Prop) (body : program Sigma Unit)
    (W : program Sigma Unit) : program Sigma Unit :=
  choice (test cond ;; body ;; W)
    (test (fun s => Not (cond s)) ;; ret ())

def whileP {Sigma : Type} (cond : Sigma -> Prop) (body : program Sigma Unit) :
    program Sigma Unit :=
  Lfix (whileP_f cond body)

def whileretP_f {Sigma A : Type} (cond : A -> Sigma -> Prop)
    (body : A -> program Sigma A) (W : A -> program Sigma A) :
    A -> program Sigma A :=
  fun a => choice
    (test (fun s => cond a s) ;; a' <- body a ;; W a')
    (test (fun s => Not (cond a s)) ;; ret a)

def whileretP {Sigma A : Type} (cond : A -> Sigma -> Prop)
    (body : A -> program Sigma A) : A -> program Sigma A :=
  Lfix (whileretP_f cond body)

def Repeat_f {Sigma : Type} (body : program Sigma Unit)
    (W : program Sigma Unit) : program Sigma Unit :=
  body ;; W

def Repeat {Sigma : Type} (body : program Sigma Unit) : program Sigma Unit :=
  Lfix (Repeat_f body)

def repeat_break_f {Sigma A B : Type}
    (body : A -> program Sigma (CntOrBrk A B))
    (W : A -> program Sigma B) (a : A) : program Sigma B :=
  x <- body a ;;
  match x with
  | .by_continue a' => W a'
  | .by_break b => ret b

def repeat_break {Sigma A B : Type}
    (body : A -> program Sigma (CntOrBrk A B)) : A -> program Sigma B :=
  Lfix (repeat_break_f body)

def repeat_break_f_noinput {Sigma B : Type}
    (body : program Sigma (CntOrBrk Unit B))
    (W : program Sigma B) : program Sigma B :=
  x <- body ;;
  match x with
  | .by_continue _ => W
  | .by_break b => ret b

def repeat_break_noin {Sigma B : Type}
    (body : program Sigma (CntOrBrk Unit B)) : program Sigma B :=
  Lfix (repeat_break_f_noinput body)

def «continue» {Sigma A B : Type} (a : A) : program Sigma (CntOrBrk A B) :=
  ret (.by_continue a)

def «break» {Sigma A B : Type} (b : B) : program Sigma (CntOrBrk A B) :=
  ret (.by_break b)

def range_iter_f {Sigma A : Type} (hi : Int)
    (body : Int -> A -> program Sigma A)
    (W : Int × A -> program Sigma A) : Int × A -> program Sigma A :=
  fun (lo, a0) => choice
    (test' (lo < hi) ;; a1 <- body lo a0 ;; W (lo + 1, a1))
    (test' (lo >= hi) ;; ret a0)

def range_iter {Sigma A : Type} (lo hi : Int)
    (body : Int -> A -> program Sigma A) : A -> program Sigma A :=
  fun a => Lfix (range_iter_f hi body) (lo, a)

def range_iter_break_f {Sigma A B : Type} (hi : Int)
    (body : Int -> A -> program Sigma (CntOrBrk A B))
    (W : Int × A -> program Sigma (CntOrBrk A B)) :
    Int × A -> program Sigma (CntOrBrk A B) :=
  fun (lo, a0) => choice
    (test' (lo < hi) ;;
      ab <- body lo a0 ;;
      match ab with
      | .by_continue a1 => W (lo + 1, a1)
      | .by_break b => «break» b)
    (test' (lo >= hi) ;; «continue» a0)

def range_iter_break {Sigma A B : Type} (lo hi : Int)
    (body : Int -> A -> program Sigma (CntOrBrk A B)) :
    A -> program Sigma (CntOrBrk A B) :=
  fun a => Lfix (range_iter_break_f hi body) (lo, a)

def forset_f {Sigma A : Type} (body : A -> program Sigma Unit)
    (W : (A -> Prop) -> program Sigma Unit) («universe» : A -> Prop) :
    program Sigma Unit :=
  choice
    (a <- get (fun _ a => «universe» a) ;;
      body a ;;
      W (fun x => «universe» x /\ Not (x = a)))
    (test' (forall x, Not («universe» x)) ;; ret ())

def forset {Sigma A : Type} («universe» : A -> Prop)
    (body : A -> program Sigma Unit) : program Sigma Unit :=
  Lfix (forset_f body) «universe»

def list_iter {Sigma A B : Type} (body : A -> B -> program Sigma B) :
    List A -> B -> program Sigma B
  | [], b => ret b
  | a :: rest, b => b0 <- body a b ;; list_iter body rest b0

theorem bind_equiv {Sigma A B : Type} (c1 c1' : program Sigma A)
    (c2 c2' : A -> program Sigma B) :
    Sets.equiv c1 c1' -> Sets.equiv c2 c2' ->
      Sets.equiv (bind c1 c2) (bind c1' c2') := by
  intro h1 h2 s b s'
  constructor
  · rintro ⟨a, s0, ha, hb⟩
    exact ⟨a, s0, h1 s a s0 |>.mp ha, h2 a s0 b s' |>.mp hb⟩
  · rintro ⟨a, s0, ha, hb⟩
    exact ⟨a, s0, h1 s a s0 |>.mpr ha, h2 a s0 b s' |>.mpr hb⟩

theorem bindpat_equiv {Sigma A B : Type} (c1 c1' : program Sigma A)
    (c2 c2' : A -> program Sigma B) :
    Sets.equiv c1 c1' -> Sets.equiv c2 c2' ->
      Sets.equiv (bind c1 fun x => c2 x) (bind c1' fun x => c2' x) :=
  bind_equiv c1 c1' c2 c2'

theorem bind_ret_left {Sigma A B : Type} (x : A) (m : A -> program Sigma B) :
    Sets.equiv (bind (ret x) m) (m x) := by
  intro s b s'
  constructor
  · rintro ⟨a, s0, ⟨rfl, rfl⟩, h⟩
    exact h
  · intro h
    exact ⟨x, s, ⟨rfl, rfl⟩, h⟩

theorem bind_ret_right {Sigma A : Type} (m : program Sigma A) :
    Sets.equiv (bind m ret) m := by
  intro s a s'
  constructor
  · rintro ⟨b, s0, h, ⟨rfl, rfl⟩⟩
    exact h
  · intro h
    exact ⟨a, s', h, ⟨rfl, rfl⟩⟩

theorem bind_assoc {Sigma A B C : Type} (c0 : program Sigma A)
    (c1 : A -> program Sigma B) (c2 : B -> program Sigma C) :
    Sets.equiv (bind (bind c0 c1) c2) (bind c0 fun x => bind (c1 x) c2) := by
  intro s c s'
  constructor
  · rintro ⟨b, s1, ⟨a, s0, h0, h1⟩, h2⟩
    exact ⟨a, s0, h0, ⟨b, s1, h1, h2⟩⟩
  · rintro ⟨a, s0, h0, b, s1, h1, h2⟩
    exact ⟨b, s1, ⟨a, s0, h0, h1⟩, h2⟩

theorem bind_fun_seq_equiv {Sigma B C D : Type}
    (c0 : D -> program Sigma Unit) (c1 : program Sigma B)
    (c2 : B -> program Sigma C) :
    Sets.equiv (fun d => x <- (c0 d ;; c1) ;; c2 x)
      (fun d => c0 d ;; x <- c1 ;; c2 x) := by
  intro d
  exact bind_assoc (c0 d) (fun _ => c1) c2

theorem bind_choice_equiv {Sigma A B : Type} (c0 c1 : program Sigma A)
    (c2 : A -> program Sigma B) :
    Sets.equiv (x <- choice c0 c1 ;; c2 x)
      (choice (x <- c0 ;; c2 x) (x <- c1 ;; c2 x)) := by
  intro s b s'
  constructor
  · rintro ⟨a, s0, h | h, hc⟩
    · exact Or.inl ⟨a, s0, h, hc⟩
    · exact Or.inr ⟨a, s0, h, hc⟩
  · rintro (⟨a, s0, h, hc⟩ | ⟨a, s0, h, hc⟩)
    · exact ⟨a, s0, Or.inl h, hc⟩
    · exact ⟨a, s0, Or.inr h, hc⟩

theorem choice_case_equiv {Sigma A : Type} (c0 c1 c2 c3 : program Sigma A) :
    Sets.equiv c0 c2 -> Sets.equiv c1 c3 ->
      Sets.equiv (choice c0 c1) (choice c2 c3) := by
  intro h0 h1 s a s'
  exact or_congr (h0 s a s') (h1 s a s')

theorem choice_comm {Sigma A : Type} (c0 c1 : program Sigma A) :
    Sets.equiv (choice c0 c1) (choice c1 c0) := by
  intro s a s'
  exact or_comm

theorem ret_equiv {Sigma A B : Type} (a : A) (c : A -> program Sigma B) :
    Sets.equiv (x <- ret a ;; c x) (c a) :=
  bind_ret_left a c

theorem ret_equiv' {Sigma A B C : Type} (f : A -> B)
    (c : A -> B -> program Sigma C) :
    Sets.equiv (fun k => x <- ret (f k) ;; c k x) (fun k => c k (f k)) := by
  intro k
  exact bind_ret_left (f k) (c k)

theorem common_step_equiv {Sigma A B : Type} (c0 : program Sigma A)
    (c1 c2 : A -> program Sigma B) (h : forall a, Sets.equiv (c1 a) (c2 a)) :
    Sets.equiv (x <- c0 ;; c1 x) (x <- c0 ;; c2 x) :=
  bind_equiv c0 c0 c1 c2 (fun _ _ _ => Iff.rfl) h

theorem choice_l_equiv {Sigma A : Type} (c0 c1 : program Sigma A)
    (h : Sets.equiv c1 (fun _ _ _ => False)) :
    Sets.equiv (choice c0 c1) c0 := by
  intro s a s'
  constructor
  · rintro (hc | hc)
    · exact hc
    · exact False.elim ((h s a s').mp hc)
  · exact Or.inl

theorem choice_r_equiv {Sigma A : Type} (c0 c1 : program Sigma A)
    (h : Sets.equiv c0 (fun _ _ _ => False)) :
    Sets.equiv (choice c0 c1) c1 := by
  intro s a s'
  constructor
  · rintro (hc | hc)
    · exact False.elim ((h s a s').mp hc)
    · exact hc
  · exact Or.inr

theorem choice_idem_equiv {Sigma A : Type} (c : program Sigma A) :
    Sets.equiv (choice c c) c := by
  intro s a s'
  constructor
  · rintro (h | h) <;> exact h
  · exact fun h => Or.inl h

def programcall {Sigma1 Sigma2 A : Type} (f : Sigma1 -> Sigma2)
    (g : Sigma2 -> Sigma1) (c : program Sigma2 A) : program Sigma1 A :=
  fun s1 a s2 => exists s0, c (f s1) a s0 /\ s2 = g s0

instance bind_congr {Sigma A B : Type} :
    Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) (@bind Sigma A B) where
  proper c1 c1' h1 c2 c2' h2 := bind_equiv c1 c1' c2 c2' h1 h2

instance programbindpat_Proper {Sigma A B : Type} :
    Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv)
      (fun (c1 : program Sigma A) (c2 : A -> program Sigma B) =>
        @bind Sigma A B c1 fun x => c2 x) where
  proper c1 c1' h1 c2 c2' h2 := bind_equiv c1 c1' c2 c2' h1 h2

instance programbind_included_Proper {Sigma A B : Type} :
    Proper (Sets.included ==> Sets.included ==> Sets.included) (@bind Sigma A B) where
  proper c1 c1' h1 c2 c2' h2 s b s' := by
    rintro ⟨a, s0, ha, hb⟩
    exact ⟨a, s0, h1 s a s0 ha, h2 a s0 b s' hb⟩

instance choice_equiv_Proper {Sigma A : Type} :
    Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) (@choice Sigma A) where
  proper c0 c0' h0 c1 c1' h1 := choice_case_equiv c0 c1 c0' c1' h0 h1

def ATrue {Sigma : Type} : Sigma -> Prop := fun _ => True

theorem program_eq_of_equiv {Sigma A : Type}
    {c1 c2 : program Sigma A} (h : Sets.equiv c1 c2) : c1 = c2 := by
  funext s a s'
  exact propext (h s a s')

private theorem bind_assoc_eq {Sigma A B C : Type} (c0 : program Sigma A)
    (c1 : A -> program Sigma B) (c2 : B -> program Sigma C) :
    bind (bind c0 c1) c2 = bind c0 (fun x => bind (c1 x) c2) :=
  program_eq_of_equiv (bind_assoc c0 c1 c2)

private theorem bind_choice_eq {Sigma A B : Type} (c0 c1 : program Sigma A)
    (c2 : A -> program Sigma B) :
    bind (choice c0 c1) c2 = choice (bind c0 c2) (bind c1 c2) :=
  program_eq_of_equiv (bind_choice_equiv c0 c1 c2)

private theorem ret_eq {Sigma A B : Type} (a : A) (c : A -> program Sigma B) :
    bind (ret a) c = c a :=
  program_eq_of_equiv (ret_equiv a c)

private theorem bind_ret_right_eq {Sigma A : Type} (c : program Sigma A) :
    bind c ret = c :=
  program_eq_of_equiv (bind_ret_right c)

macro "state_prog_nf" : tactic =>
  `(tactic|
    try simp only [MonadLib.bind, MonadLib.ret, StateRelMonad.state_rel_monad,
      StateRelMonad.bind_assoc_eq, StateRelMonad.bind_choice_eq,
      StateRelMonad.ret_eq, StateRelMonad.bind_ret_right_eq])

macro "state_prog_nf" " in " loc:Lean.Parser.Tactic.locationHyp : tactic =>
  `(tactic|
    try simp only [MonadLib.bind, MonadLib.ret, StateRelMonad.state_rel_monad,
      StateRelMonad.bind_assoc_eq, StateRelMonad.bind_choice_eq,
      StateRelMonad.ret_eq, StateRelMonad.bind_ret_right_eq] at $loc)

end MonadLib.StateRelMonad
