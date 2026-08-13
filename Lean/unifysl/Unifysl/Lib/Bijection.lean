import Std

namespace Unifysl

def image_defined {A : Type u} {B : Type v} (R : A -> B -> Prop) : Prop :=
  forall a, exists b, R a b

def partial_functional {A : Type u} {B : Type v} (R : A -> B -> Prop) : Prop :=
  forall a b1 b2, R a b1 -> R a b2 -> b1 = b2

def injective {A : Type u} {B : Type v} (R : A -> B -> Prop) : Prop :=
  forall a1 a2 b, R a1 b -> R a2 b -> a1 = a2

def surjective {A : Type u} {B : Type v} (R : A -> B -> Prop) : Prop :=
  forall b, exists a, R a b

def function_injective {A : Type u} {B : Type v} (f : A -> B) : Prop :=
  forall a1 a2, f a1 = f a2 -> a1 = a2

def function_surjective {A : Type u} {B : Type v} (f : A -> B) : Prop :=
  forall b, exists a, f a = b

structure injection (A : Type u) (B : Type v) : Type (max u v) where
  inj_R : A -> B -> Prop
  im_inj : image_defined inj_R
  pf_inj : partial_functional inj_R
  in_inj : injective inj_R

instance {A : Type u} {B : Type v} : CoeFun (injection A B) (fun _ => A -> B -> Prop) where
  coe R := R.inj_R

structure surjection (A : Type u) (B : Type v) : Type (max u v) where
  sur_R : A -> B -> Prop
  im_surj : image_defined sur_R
  pf_surj : partial_functional sur_R
  su_surj : surjective sur_R

instance {A : Type u} {B : Type v} : CoeFun (surjection A B) (fun _ => A -> B -> Prop) where
  coe R := R.sur_R

structure bijection (A : Type u) (B : Type v) : Type (max u v) where
  bij_R : A -> B -> Prop
  im_bij : image_defined bij_R
  pf_bij : partial_functional bij_R
  in_bij : injective bij_R
  su_bij : surjective bij_R

instance {A : Type u} {B : Type v} : CoeFun (bijection A B) (fun _ => A -> B -> Prop) where
  coe R := R.bij_R

export injection (inj_R im_inj pf_inj in_inj)
export surjection (sur_R im_surj pf_surj su_surj)
export bijection (bij_R im_bij pf_bij in_bij su_bij)

def FBuild_injection (A : Type u) (B : Type v) (f : A -> B)
    (H : function_injective f) : injection A B :=
  { inj_R := fun a b => f a = b
    im_inj := by intro a; exact Exists.intro (f a) rfl
    pf_inj := by
      intro a b1 b2 h1 h2
      exact h1.symm.trans h2
    in_inj := by
      intro a1 a2 b h1 h2
      apply H
      exact h1.trans h2.symm }

def FBuild_surjection (A : Type u) (B : Type v) (f : A -> B)
    (H : function_surjective f) : surjection A B :=
  { sur_R := fun a b => f a = b
    im_surj := by intro a; exact Exists.intro (f a) rfl
    pf_surj := by
      intro a b1 b2 h1 h2
      exact h1.symm.trans h2
    su_surj := H }

def FBuild_bijection (A : Type u) (B : Type v) (f : A -> B)
    (H : function_injective f) (H0 : function_surjective f) : bijection A B :=
  { bij_R := fun a b => f a = b
    im_bij := by intro a; exact Exists.intro (f a) rfl
    pf_bij := by
      intro a b1 b2 h1 h2
      exact h1.symm.trans h2
    in_bij := by
      intro a1 a2 b h1 h2
      apply H
      exact h1.trans h2.symm
    su_bij := H0 }

def injection_trans {A : Type u} {B : Type v} {C : Type w}
    (R1 : injection A B) (R2 : injection B C) : injection A C :=
  { inj_R := fun a c => exists b, R1 a b /\ R2 b c
    im_inj := by
      intro a
      cases R1.im_inj a with
      | intro b hb =>
          cases R2.im_inj b with
          | intro c hc =>
              exact Exists.intro c (Exists.intro b (And.intro hb hc))
    pf_inj := by
      intro a c1 c2 h1 h2
      cases h1 with
      | intro b1 h1 =>
          cases h1 with
          | intro hb1 hc1 =>
              cases h2 with
              | intro b2 h2 =>
                  cases h2 with
                  | intro hb2 hc2 =>
                      have hb : b1 = b2 := R1.pf_inj a b1 b2 hb1 hb2
                      subst b2
                      exact R2.pf_inj b1 c1 c2 hc1 hc2
    in_inj := by
      intro a1 a2 c h1 h2
      cases h1 with
      | intro b1 h1 =>
          cases h1 with
          | intro ha1 hb1 =>
              cases h2 with
              | intro b2 h2 =>
                  cases h2 with
                  | intro ha2 hb2 =>
                      have hb : b1 = b2 := R2.in_inj b1 b2 c hb1 hb2
                      subst b2
                      exact R1.in_inj a1 a2 b1 ha1 ha2 }

def bijection_sym {A : Type u} {B : Type v} (R : bijection A B) : bijection B A :=
  { bij_R := fun a b => R b a
    im_bij := R.su_bij
    pf_bij := by
      intro a b1 b2 h1 h2
      exact R.in_bij b1 b2 a h1 h2
    in_bij := by
      intro a1 a2 b h1 h2
      exact R.pf_bij b a1 a2 h1 h2
    su_bij := R.im_bij }

def bijection_refl {A : Type u} : bijection A A :=
  { bij_R := Eq
    im_bij := by intro a; exact Exists.intro a rfl
    pf_bij := by intro a b1 b2 h1 h2; exact h1.symm.trans h2
    in_bij := by intro a1 a2 b h1 h2; exact h1.trans h2.symm
    su_bij := by intro b; exact Exists.intro b rfl }

def sum_injection {A1 : Type u1} {B1 : Type v1} {A2 : Type u2} {B2 : Type v2}
    (R1 : injection A1 B1) (R2 : injection A2 B2) :
    injection (Sum A1 A2) (Sum B1 B2) :=
  { inj_R := fun a b =>
      match a, b with
      | Sum.inl a, Sum.inl b => R1 a b
      | Sum.inr a, Sum.inr b => R2 a b
      | _, _ => False
    im_inj := by
      intro a
      cases a with
      | inl a =>
          cases R1.im_inj a with
          | intro b hb =>
              exact Exists.intro (Sum.inl b) hb
      | inr a =>
          cases R2.im_inj a with
          | intro b hb =>
              exact Exists.intro (Sum.inr b) hb
    pf_inj := by
      intro a b1 b2 h1 h2
      cases a with
      | inl a =>
          cases b1 with
          | inl b1 =>
              cases b2 with
              | inl b2 =>
                  have hb : b1 = b2 := R1.pf_inj a b1 b2 h1 h2
                  cases hb
                  rfl
              | inr _ => cases h2
          | inr _ => cases h1
      | inr a =>
          cases b1 with
          | inl _ => cases h1
          | inr b1 =>
              cases b2 with
              | inl _ => cases h2
              | inr b2 =>
                  have hb : b1 = b2 := R2.pf_inj a b1 b2 h1 h2
                  cases hb
                  rfl
    in_inj := by
      intro a1 a2 b h1 h2
      cases a1 with
      | inl a1 =>
          cases a2 with
          | inl a2 =>
              cases b with
              | inl b =>
                  have ha : a1 = a2 := R1.in_inj a1 a2 b h1 h2
                  cases ha
                  rfl
              | inr _ => cases h1
          | inr _ =>
              cases b with
              | inl _ => cases h2
              | inr _ => cases h1
      | inr a1 =>
          cases a2 with
          | inl _ =>
              cases b with
              | inl _ => cases h1
              | inr _ => cases h2
          | inr a2 =>
              cases b with
              | inl _ => cases h1
              | inr b =>
                  have ha : a1 = a2 := R2.in_inj a1 a2 b h1 h2
                  cases ha
                  rfl }

def prod_injection {A1 : Type u1} {B1 : Type v1} {A2 : Type u2} {B2 : Type v2}
    (R1 : injection A1 B1) (R2 : injection A2 B2) :
    injection (Prod A1 A2) (Prod B1 B2) :=
  { inj_R := fun a b => R1 a.fst b.fst /\ R2 a.snd b.snd
    im_inj := by
      intro a
      cases R1.im_inj a.fst with
      | intro b1 hb1 =>
          cases R2.im_inj a.snd with
          | intro b2 hb2 =>
              exact Exists.intro (b1, b2) (And.intro hb1 hb2)
    pf_inj := by
      intro a b1 b2 h1 h2
      cases b1 with
      | mk b11 b12 =>
          cases b2 with
          | mk b21 b22 =>
              cases h1 with
              | intro hb11 hb12 =>
                  cases h2 with
                  | intro hb21 hb22 =>
                      have hfst : b11 = b21 := R1.pf_inj a.fst b11 b21 hb11 hb21
                      have hsnd : b12 = b22 := R2.pf_inj a.snd b12 b22 hb12 hb22
                      cases hfst
                      cases hsnd
                      rfl
    in_inj := by
      intro a1 a2 b h1 h2
      cases a1 with
      | mk a11 a12 =>
          cases a2 with
          | mk a21 a22 =>
              cases h1 with
              | intro ha11 ha12 =>
                  cases h2 with
                  | intro ha21 ha22 =>
                      have hfst : a11 = a21 := R1.in_inj a11 a21 b.fst ha11 ha21
                      have hsnd : a12 = a22 := R2.in_inj a12 a22 b.snd ha12 ha22
                      cases hfst
                      cases hsnd
                      rfl }

def sigT_injection (I : Type u) (A : I -> Type v) (B : Type w)
    (R : forall i : I, injection (A i) B) : injection (Sigma A) (Prod I B) :=
  { inj_R := fun a b => a.1 = b.fst /\ (R a.1) a.2 b.snd
    im_inj := by
      intro a
      cases a with
      | mk i a0 =>
          cases (R i).im_inj a0 with
          | intro b0 hb0 =>
              exact Exists.intro (i, b0) (And.intro rfl hb0)
    pf_inj := by
      intro a b1 b2 h1 h2
      cases b1 with
      | mk i1 b1 =>
          cases b2 with
          | mk i2 b2 =>
              cases h1 with
              | intro hi1 hb1 =>
                  cases h2 with
                  | intro hi2 hb2 =>
                      cases hi1
                      cases hi2
                      have hb : b1 = b2 := (R a.1).pf_inj a.2 b1 b2 hb1 hb2
                      cases hb
                      rfl
    in_inj := by
      intro a1 a2 b h1 h2
      cases b with
      | mk i b =>
          cases a1 with
          | mk i1 x1 =>
              cases a2 with
              | mk i2 x2 =>
                  cases h1 with
                  | intro hi1 hb1 =>
                      cases h2 with
                      | intro hi2 hb2 =>
                          cases hi1
                          cases hi2
                          have hx : x1 = x2 := (R i).in_inj x1 x2 b hb1 hb2
                          cases hx
                          rfl }

def bijection_injection {A : Type u} {B : Type v} (R : bijection A B) : injection A B :=
  { inj_R := R
    im_inj := R.im_bij
    pf_inj := R.pf_bij
    in_inj := R.in_bij }

private theorem nat2_even_or_odd :
    forall m : Nat, (exists n, m = n + n) \/ (exists n, m = n + n + 1)
  | 0 => Or.inl (Exists.intro 0 rfl)
  | m + 1 =>
      match nat2_even_or_odd m with
      | Or.inl h =>
          match h with
          | Exists.intro n hn => Or.inr (Exists.intro n (by omega))
      | Or.inr h =>
          match h with
          | Exists.intro n hn => Or.inl (Exists.intro (n + 1) (by omega))

def nat2_nat_bijection : bijection (Sum Nat Nat) Nat :=
  { bij_R := fun n m =>
      match n with
      | Sum.inl n => m = n + n
      | Sum.inr n => m = n + n + 1
    im_bij := by
      intro a
      cases a with
      | inl n => exact Exists.intro (n + n) rfl
      | inr n => exact Exists.intro (n + n + 1) rfl
    pf_bij := by
      intro a b1 b2 h1 h2
      cases a <;> exact h1.trans h2.symm
    in_bij := by
      intro a1 a2 b h1 h2
      cases a1 with
      | inl n1 =>
          cases a2 with
          | inl n2 =>
              simp at h1 h2
              have hn : n1 = n2 := by omega
              cases hn
              rfl
          | inr n2 =>
              simp at h1 h2
              omega
      | inr n1 =>
          cases a2 with
          | inl n2 =>
              simp at h1 h2
              omega
          | inr n2 =>
              simp at h1 h2
              have hn : n1 = n2 := by omega
              cases hn
              rfl
    su_bij := by
      intro b
      cases nat2_even_or_odd b with
      | inl h =>
          cases h with
          | intro n hn => exact Exists.intro (Sum.inl n) hn
      | inr h =>
          cases h with
          | intro n hn => exact Exists.intro (Sum.inr n) hn }

def triangular_sum : Nat -> Nat
  | 0 => 0
  | n + 1 => (n + 1) + triangular_sum n

private theorem triangular_sum_le_succ (n : Nat) :
    triangular_sum n <= triangular_sum (n + 1) := by
  simp [triangular_sum]

private theorem triangular_sum_mono {a b : Nat} (h : a <= b) :
    triangular_sum a <= triangular_sum b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step h ih =>
      exact Nat.le_trans ih (triangular_sum_le_succ _)

private theorem triangular_sum_encode_lt_next {i j : Nat} :
    triangular_sum (i + j) + i < triangular_sum (i + j + 1) := by
  simp [triangular_sum]
  omega

private theorem triangular_sum_same_diagonal {i1 j1 i2 j2 : Nat}
    (h : triangular_sum (i1 + j1) + i1 =
      triangular_sum (i2 + j2) + i2) :
    i1 + j1 = i2 + j2 := by
  have hnot12 : Not (i1 + j1 < i2 + j2) := by
    intro hlt
    have hsucc : i1 + j1 + 1 <= i2 + j2 := by omega
    have hmono : triangular_sum (i1 + j1 + 1) <= triangular_sum (i2 + j2) :=
      triangular_sum_mono hsucc
    have hright : triangular_sum (i2 + j2) <= triangular_sum (i2 + j2) + i2 := by
      omega
    have hlt_code :
        triangular_sum (i1 + j1) + i1 < triangular_sum (i2 + j2) + i2 :=
      Nat.lt_of_lt_of_le triangular_sum_encode_lt_next (Nat.le_trans hmono hright)
    rw [h] at hlt_code
    exact Nat.lt_irrefl (triangular_sum (i2 + j2) + i2) hlt_code
  have hnot21 : Not (i2 + j2 < i1 + j1) := by
    intro hlt
    have hsucc : i2 + j2 + 1 <= i1 + j1 := by omega
    have hmono : triangular_sum (i2 + j2 + 1) <= triangular_sum (i1 + j1) :=
      triangular_sum_mono hsucc
    have hright : triangular_sum (i1 + j1) <= triangular_sum (i1 + j1) + i1 := by
      omega
    have hlt_code :
        triangular_sum (i2 + j2) + i2 < triangular_sum (i1 + j1) + i1 :=
      Nat.lt_of_lt_of_le triangular_sum_encode_lt_next (Nat.le_trans hmono hright)
    rw [h] at hlt_code
    exact Nat.lt_irrefl (triangular_sum (i2 + j2) + i2) hlt_code
  omega

private theorem triangular_sum_pair_surj :
    forall m : Nat, exists p : Prod Nat Nat,
      m = triangular_sum (p.1 + p.2) + p.1
  | 0 => Exists.intro (0, 0) rfl
  | m + 1 =>
      match triangular_sum_pair_surj m with
      | Exists.intro p hp =>
          match p with
          | (i, j) =>
              match j with
              | 0 =>
                  Exists.intro (0, i + 1) (by
                    simp [triangular_sum] at hp ⊢
                    omega)
              | j0 + 1 =>
                  Exists.intro (i + 1, j0) (by
                    simp at hp ⊢
                    have hsum : (i + 1) + j0 = i + (j0 + 1) := by omega
                    rw [hsum]
                    omega)

def natnat_nat_bijection : bijection (Prod Nat Nat) Nat :=
  { bij_R := fun n m =>
      m = match n with
        | (n1, n2) => triangular_sum (n1 + n2) + n1
    im_bij := by
      intro a
      exact Exists.intro (triangular_sum (a.1 + a.2) + a.1) rfl
    pf_bij := by
      intro a b1 b2 h1 h2
      exact h1.trans h2.symm
    in_bij := by
      intro a1 a2 b h1 h2
      cases a1 with
      | mk i1 j1 =>
          cases a2 with
          | mk i2 j2 =>
              simp at h1 h2
              have hcode :
                  triangular_sum (i1 + j1) + i1 =
                    triangular_sum (i2 + j2) + i2 :=
                h1.symm.trans h2
              have hsum : i1 + j1 = i2 + j2 :=
                triangular_sum_same_diagonal hcode
              have hcode_same :
                  triangular_sum (i1 + j1) + i1 =
                    triangular_sum (i1 + j1) + i2 := by
                simpa [hsum] using hcode
              have hi : i1 = i2 := by omega
              have hj : j1 = j2 := by omega
              cases hi
              cases hj
              rfl
    su_bij := by
      intro b
      exact triangular_sum_pair_surj b }

end Unifysl
