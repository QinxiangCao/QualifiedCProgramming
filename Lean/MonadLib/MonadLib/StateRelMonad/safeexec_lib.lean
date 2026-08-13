import MonadLib.StateRelMonad.StateRelHoare

namespace MonadLib.StateRelMonad

open AUXLib
open scoped MonadNotation

def safe {Sigma A : Type} (s : Sigma) (c : program Sigma A)
    (X : A -> Sigma -> Prop) : Prop :=
  forall a s', c s a s' -> X a s'

def safeExec {Sigma A : Type} (P : Sigma -> Prop) (c : program Sigma A)
    (X : A -> Sigma -> Prop) : Prop :=
  exists s, P s /\ safe s c X

def result_state {Sigma A : Type} (P : Sigma -> Prop)
    (c : program Sigma A) : A -> Sigma -> Prop :=
  fun a s1 => exists s0, P s0 /\ c s0 a s1

def hs_eval {Sigma A : Type} (c : program Sigma A) (P P' : Sigma -> Prop)
    (a : A) : Prop :=
  forall s, P s -> exists s', c s a s' /\ P' s'

namespace StateRelMonadNotation

scoped notation:70 P " -@ " c " -⥅ " P' " ♯ " a => hs_eval c P P' a
scoped notation:70 P " -@ " c " -→ " P' => exists a, hs_eval c P P' a

end StateRelMonadNotation

abbrev asrt {Sigma : Type} : Type := Sigma -> Prop

theorem hs_eval_equiv_angelic_triple {Sigma A : Type}
    (c : program Sigma A) (P : Sigma -> Prop) (a : A) (Q : Sigma -> Prop) :
    hs_eval c P Q a <->
      valid_angelic_triple P c (fun r s => r = a /\ Q s) := by
  constructor
  · intro h s hp
    rcases h s hp with ⟨s', hc, hq⟩
    exact ⟨a, s', hc, rfl, hq⟩
  · intro h s hp
    rcases h s hp with ⟨r, s', hc, rfl, hq⟩
    exact ⟨s', hc, hq⟩

theorem highstepbind_derive {Sigma A B : Type}
    (c1 : program Sigma A) (c2 : A -> program Sigma B)
    (P : Sigma -> Prop) (a : A) (P' : Sigma -> Prop) :
    hs_eval c1 P P' a ->
    forall X, safeExec P (x <- c1 ;; c2 x) X -> safeExec P' (c2 a) X := by
  intro he X
  rintro ⟨s, hp, hs⟩
  rcases he s hp with ⟨s', hc1, hp'⟩
  exact ⟨s', hp', fun b s'' hc2 => hs b s'' ⟨a, s', hc1, hc2⟩⟩

theorem highstepseq_derive {Sigma A B : Type}
    (c1 : program Sigma A) (c2 : program Sigma B)
    (P P' : Sigma -> Prop) :
    (exists a, hs_eval c1 P P' a) ->
    forall X, safeExec P (c1 ;; c2) X -> safeExec P' c2 X := by
  rintro ⟨a, h⟩ X hs
  exact highstepbind_derive c1 (fun _ => c2) P a P' h X hs

theorem hseval_stateless_ret {A : Type} (m : program Unit A) (a : A) :
    m () a () -> hs_eval m ATrue ATrue a := by
  intro hm _ _
  exact ⟨(), hm, trivial⟩

theorem ret_eq {Sigma A : Type} (s s0 : Sigma) (a a0 : A) :
    ret a s a0 s0 <-> s = s0 /\ a0 = a := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1⟩

theorem highstependret_derive {Sigma A : Type}
    (c1 : program Sigma A) (P : Sigma -> Prop) (a : A)
    (P' : A -> Sigma -> Prop) :
    hs_eval c1 P (P' a) a ->
    forall X, safeExec P c1 X -> safeExec (P' a) (ret a) X := by
  intro he X
  rintro ⟨s, hp, hs⟩
  rcases he s hp with ⟨s', hc, hp'⟩
  exact ⟨s', hp', fun _ _ hret => by
    rcases hret with ⟨rfl, rfl⟩
    exact hs _ _ hc⟩

theorem highstepend_derive {Sigma : Type} (c1 : program Sigma Unit)
    (P P' : Sigma -> Prop) :
    (exists a, hs_eval c1 P P' a) ->
    forall X, safeExec P c1 X -> safeExec P' (ret ()) X := by
  rintro ⟨a, he⟩ X hs
  cases a
  exact highstependret_derive c1 P () (fun _ => P') he X hs

theorem highret_eval1 {Sigma A : Type} (P : Sigma -> Prop) (a : A) :
    exists r, hs_eval (ret a) P P r := by
  exact ⟨a, fun s hp => ⟨s, ⟨rfl, rfl⟩, hp⟩⟩

theorem highret_eval2 {Sigma A : Type} (P : Sigma -> Prop) (a : A) :
    hs_eval (ret a) P P a := by
  intro s hp
  exact ⟨s, ⟨rfl, rfl⟩, hp⟩

theorem hsevalbind_derive {Sigma A B : Type}
    (c1 : program Sigma A) (c2 : A -> program Sigma B)
    (P : Sigma -> Prop) (P' : A -> Sigma -> Prop) (a : A)
    (Q : B -> Sigma -> Prop) (b : B) :
    hs_eval c1 P (P' a) a -> hs_eval (c2 a) (P' a) (Q b) b ->
      hs_eval (x <- c1 ;; c2 x) P (Q b) b := by
  intro h1 h2 s hp
  rcases h1 s hp with ⟨s1, hc1, hp'⟩
  rcases h2 s1 hp' with ⟨s2, hc2, hq⟩
  exact ⟨s2, ⟨a, s1, hc1, hc2⟩, hq⟩

theorem hsevalbind_derive' {Sigma A B : Type}
    (c1 : program Sigma A) (c2 : A -> program Sigma B)
    (P P' : Sigma -> Prop) (a : A) (Q : Sigma -> Prop) (b : B) :
    hs_eval c1 P P' a -> hs_eval (c2 a) P' Q b ->
      hs_eval (x <- c1 ;; c2 x) P Q b := by
  intro h1 h2 s hp
  rcases h1 s hp with ⟨s1, hc1, hp'⟩
  rcases h2 s1 hp' with ⟨s2, hc2, hq⟩
  exact ⟨s2, ⟨a, s1, hc1, hc2⟩, hq⟩

theorem hsevalchoice_left_derive {Sigma A : Type}
    (c1 c2 : program Sigma A) (P Q : Sigma -> Prop) (a : A) :
    hs_eval c1 P Q a -> hs_eval (choice c1 c2) P Q a := by
  intro h s hp
  rcases h s hp with ⟨s', hc, hq⟩
  exact ⟨s', Or.inl hc, hq⟩

theorem hsevalchoice_right_derive {Sigma A : Type}
    (c1 c2 : program Sigma A) (P Q : Sigma -> Prop) (a : A) :
    hs_eval c2 P Q a -> hs_eval (choice c1 c2) P Q a := by
  intro h s hp
  rcases h s hp with ⟨s', hc, hq⟩
  exact ⟨s', Or.inr hc, hq⟩

theorem hsevaltest_derive {Sigma : Type} (P : Sigma -> Prop)
    (Q : Prop) (a : Unit) : Q -> hs_eval (test' Q) P P a := by
  intro hq s hp
  exact ⟨s, ⟨hq, rfl⟩, hp⟩

theorem hsevaltestbind_derive {Sigma B : Type} (P R : Sigma -> Prop)
    (Q : Prop) (c : Unit -> program Sigma B) (b : B) :
    Q -> hs_eval (c ()) P R b ->
      hs_eval (x <- test' Q ;; c x) P R b := by
  intro hq hc
  exact hsevalbind_derive' (test' Q) c P P () R b
    (hsevaltest_derive P Q () hq) hc

theorem hs_eval_proequiv {Sigma A : Type} (c1 c2 : program Sigma A)
    (P Q : Sigma -> Prop) (a : A) :
    Sets.equiv c1 c2 -> hs_eval c1 P Q a -> hs_eval c2 P Q a := by
  intro he h s hp
  rcases h s hp with ⟨s', hc, hq⟩
  exact ⟨s', (he s a s').mp hc, hq⟩

theorem safeExec_ex {Sigma A B : Type} (P : A -> Sigma -> Prop)
    (c : program Sigma B) (X : B -> Sigma -> Prop) :
    (exists a, safeExec (P a) c X) <->
      safeExec (fun s => exists a, P a s) c X := by
  constructor
  · rintro ⟨a, s, hp, hs⟩
    exact ⟨s, ⟨a, hp⟩, hs⟩
  · rintro ⟨s, ⟨a, hp⟩, hs⟩
    exact ⟨a, s, hp, hs⟩

theorem safeExec_prorefine {Sigma A : Type} (c1 c2 : program Sigma A)
    (P : Sigma -> Prop) (X : A -> Sigma -> Prop) :
    Sets.included c2 c1 -> safeExec P c1 X -> safeExec P c2 X := by
  intro hi
  rintro ⟨s, hp, hs⟩
  exact ⟨s, hp, fun a s' hc => hs a s' (hi s a s' hc)⟩

theorem safeExec_X_subset {Sigma A : Type} (c : program Sigma A)
    (P : Sigma -> Prop) (X1 X2 : A -> Sigma -> Prop) :
    Sets.included X1 X2 -> safeExec P c X1 -> safeExec P c X2 := by
  intro hi
  rintro ⟨s, hp, hs⟩
  exact ⟨s, hp, fun a s' hc => hi a s' (hs a s' hc)⟩

instance safeExec_programrefine_impl_Proper {Sigma A : Type}
    (P : Sigma -> Prop) :
    Proper (Sets.included ==> Eq ==> flipRel ImplRel) (@safeExec Sigma A P) where
  proper c1 c2 hc X1 X2 hX := by
    subst X2
    exact safeExec_prorefine c2 c1 P X1 hc

instance safeExec_X_subset_impl_Proper {Sigma A : Type} (P : Sigma -> Prop) :
    Proper (Eq ==> Sets.included ==> ImplRel) (@safeExec Sigma A P) where
  proper c1 c2 hc X1 X2 hX := by
    subst c2
    exact safeExec_X_subset c1 P X1 X2 hX

instance hseval_programequiv_Proper {Sigma A : Type} :
    Proper (Sets.equiv ==> Eq ==> Eq ==> Eq ==> Iff) (@hs_eval Sigma A) where
  proper c1 c2 hc P1 P2 hP Q1 Q2 hQ a1 a2 ha := by
    subst P2
    subst Q2
    subst a2
    exact ⟨hs_eval_proequiv c1 c2 P1 Q1 a1 hc,
      hs_eval_proequiv c2 c1 P1 Q1 a1 (AUXLib.Equivalence.symm _ _ hc)⟩

instance hseval_programequiv_Proper' {Sigma A : Type} :
    Proper (Sets.equiv ==> Eq ==> Eq ==> Eq ==> Iff) (@hs_eval Sigma A) :=
  hseval_programequiv_Proper

theorem safeExec_proequiv {Sigma A : Type} (c1 c2 : program Sigma A)
    (P : Sigma -> Prop) (X : A -> Sigma -> Prop) :
    Sets.equiv c1 c2 -> safeExec P c1 X -> safeExec P c2 X := by
  intro he
  rintro ⟨s, hp, hs⟩
  exact ⟨s, hp, fun a s' hc => hs a s' ((he s a s').mpr hc)⟩

instance safeExec_programequiv_iff_Proper {Sigma A : Type}
    (P : Sigma -> Prop) :
    Proper (Sets.equiv ==> Eq ==> Iff) (@safeExec Sigma A P) where
  proper c1 c2 hc X1 X2 hX := by
    subst X2
    exact ⟨safeExec_proequiv c1 c2 P X1 hc,
      safeExec_proequiv c2 c1 P X1 (AUXLib.Equivalence.symm _ _ hc)⟩

instance safeExec_programequiv_iff_Proper' {Sigma A : Type}
    (P : Sigma -> Prop) :
    Proper (Sets.equiv ==> Eq ==> Iff) (@safeExec Sigma A P) :=
  safeExec_programequiv_iff_Proper P

theorem safeExec_choice_l {Sigma A : Type} (c1 c2 : program Sigma A)
    (P : Sigma -> Prop) (X : A -> Sigma -> Prop) :
    safeExec P (choice c1 c2) X -> safeExec P c1 X := by
  rintro ⟨s, hp, hs⟩
  exact ⟨s, hp, fun a s' hc => hs a s' (Or.inl hc)⟩

theorem safeExec_choice_r {Sigma A : Type} (c1 c2 : program Sigma A)
    (P : Sigma -> Prop) (X : A -> Sigma -> Prop) :
    safeExec P (choice c1 c2) X -> safeExec P c2 X := by
  rintro ⟨s, hp, hs⟩
  exact ⟨s, hp, fun a s' hc => hs a s' (Or.inr hc)⟩

theorem safeExec_test' {Sigma : Type} (Q : Prop) (P : Sigma -> Prop)
    (X : Unit -> Sigma -> Prop) :
    Q -> safeExec P (test' Q) X -> safeExec P (ret ()) X := by
  intro hq
  rintro ⟨s, hp, hs⟩
  exact ⟨s, hp, fun _ _ hret => by
    rcases hret with ⟨rfl, rfl⟩
    exact hs () s ⟨hq, rfl⟩⟩

theorem safeExec_testst {Sigma : Type} (Q P : Sigma -> Prop)
    (X : Unit -> Sigma -> Prop) :
    (forall s, P s -> Q s) ->
    safeExec P (test Q) X -> safeExec P (ret ()) X := by
  intro hpq
  rintro ⟨s, hp, hs⟩
  exact ⟨s, hp, fun _ _ hret => by
    rcases hret with ⟨rfl, rfl⟩
    exact hs () s ⟨hpq s hp, rfl⟩⟩

theorem safeExec_any {Sigma A : Type} (P : Sigma -> Prop)
    (X : A -> Sigma -> Prop) (a : A) :
    safeExec P (any A) X -> safeExec P (ret a) X := by
  rintro ⟨s, hp, hs⟩
  exact ⟨s, hp, fun _ _ hret => by
    rcases hret with ⟨rfl, rfl⟩
    exact hs _ _ rfl⟩

theorem safeExec_get {Sigma A : Type} (Pa : Sigma -> A -> Prop)
    (P : Sigma -> Prop) (X : A -> Sigma -> Prop) (a : A) :
    (forall s, P s -> Pa s a) ->
    safeExec P (get Pa) X -> safeExec P (ret a) X := by
  intro hpa
  rintro ⟨s, hp, hs⟩
  exact ⟨s, hp, fun _ _ hret => by
    rcases hret with ⟨rfl, rfl⟩
    exact hs _ _ ⟨hpa s hp, rfl⟩⟩

theorem safeExec_get' {Sigma A : Type} (f : Sigma -> A)
    (P : Sigma -> Prop) (X : A -> Sigma -> Prop) (a : A) :
    (forall s, P s -> a = f s) ->
    safeExec P (get' f) X -> safeExec P (ret a) X := by
  exact safeExec_get (fun s r => r = f s) P X a

theorem safeExec_update' {Sigma : Type} (f : Sigma -> Sigma)
    (P : Sigma -> Prop) (X : Unit -> Sigma -> Prop) :
    safeExec P (update' f) X ->
      safeExec (fun s => exists s0, s = f s0 /\ P s0) (ret ()) X := by
  rintro ⟨s, hp, hs⟩
  refine ⟨f s, ⟨s, rfl, hp⟩, ?_⟩
  intro _ s' hret
  rcases hret with ⟨rfl, rfl⟩
  exact hs () (f s) rfl

theorem safeExec_update {Sigma : Type} (R : Sigma -> Sigma -> Prop)
    (P : Sigma -> Prop) (X : Unit -> Sigma -> Prop) :
    (forall s, P s -> exists s', R s s') ->
    safeExec P (update R) X ->
      safeExec (fun s => exists s0, R s0 s /\ P s0) (ret ()) X := by
  intro hex
  rintro ⟨s, hp, hs⟩
  rcases hex s hp with ⟨s', hr⟩
  refine ⟨s', ⟨s, hr, hp⟩, ?_⟩
  intro _ s'' hret
  rcases hret with ⟨rfl, rfl⟩
  exact hs () s' hr

theorem safeExec_bind_reta {Sigma A B : Type}
    (c1 : program Sigma A) (c2 : A -> program Sigma B)
    (P P' : Sigma -> Prop) (a : A) :
    (forall X, safeExec P c1 X -> safeExec P' (ret a) X) ->
    forall X, safeExec P (x <- c1 ;; c2 x) X -> safeExec P' (c2 a) X := by
  intro h X
  rintro ⟨s, hp, hs⟩
  let X' : A -> Sigma -> Prop := fun r s' => safe s' (c2 r) X
  have hc1 : safeExec P c1 X' := ⟨s, hp, fun r s' hc1 b s'' hc2 =>
    hs b s'' ⟨r, s', hc1, hc2⟩⟩
  rcases h X' hc1 with ⟨s', hp', hret⟩
  exact ⟨s', hp', hret a s' ⟨rfl, rfl⟩⟩

theorem safeExec_bind' {Sigma A B : Type}
    (c1 : program Sigma A) (c2 : A -> program Sigma B)
    (P P' : Sigma -> Prop) :
    (forall X, safeExec P c1 X -> exists a, safeExec P' (ret a) X) ->
    forall X, safeExec P (x <- c1 ;; c2 x) X ->
      exists a, safeExec P' (c2 a) X := by
  intro h X hs
  let X' : A -> Sigma -> Prop := fun r s' => safe s' (c2 r) X
  have hc1 : safeExec P c1 X' := by
    rcases hs with ⟨s, hp, hbind⟩
    exact ⟨s, hp, fun r s' hc b s'' hc2 => hbind b s'' ⟨r, s', hc, hc2⟩⟩
  rcases h X' hc1 with ⟨a, s', hp', hret⟩
  exact ⟨a, s', hp', hret a s' ⟨rfl, rfl⟩⟩

theorem safeExec_bind {Sigma A B : Type}
    (c1 : program Sigma A) (c2 : A -> program Sigma B)
    (P : Sigma -> Prop) (X : B -> Sigma -> Prop) :
    safeExec P (x <- c1 ;; c2 x) X ->
    exists X', safeExec P c1 X' /\
      forall P' a, safeExec P' (ret a) X' -> safeExec P' (c2 a) X := by
  rintro ⟨s, hp, hbind⟩
  let X' : A -> Sigma -> Prop := fun r s' => c1 s r s'
  refine ⟨X', ⟨s, hp, fun r s' hc => hc⟩, ?_⟩
  intro P' a
  rintro ⟨s', hp', hret⟩
  have hc1 : c1 s a s' := hret a s' ⟨rfl, rfl⟩
  exact ⟨s', hp', fun b s'' hc2 => hbind b s'' ⟨a, s', hc1, hc2⟩⟩

theorem safeExec_conseq {Sigma A : Type} (P' P : Sigma -> Prop)
    (c : program Sigma A) (X : A -> Sigma -> Prop) :
    safeExec P c X -> (forall s, P s -> P' s) -> safeExec P' c X := by
  rintro ⟨s, hp, hs⟩ h
  exact ⟨s, h s hp, hs⟩

theorem safeExec_test_bind {Sigma A : Type} (Q : Prop)
    (c : program Sigma A) (P : Sigma -> Prop) (X : A -> Sigma -> Prop) :
    Q -> safeExec P (test' Q ;; c) X -> safeExec P c X := by
  intro hq hs
  exact safeExec_bind_reta (test' Q) (fun _ => c) P P ()
    (fun Y h => safeExec_test' Q P Y hq h) X hs

theorem safeExec_testst_bind {Sigma A : Type} (Q : Sigma -> Prop)
    (c : program Sigma A) (P : Sigma -> Prop) (X : A -> Sigma -> Prop) :
    (forall s, P s -> Q s) ->
    safeExec P (test Q ;; c) X -> safeExec P c X := by
  intro hq hs
  exact safeExec_bind_reta (test Q) (fun _ => c) P P ()
    (fun Y h => safeExec_testst Q P Y hq h) X hs

theorem safeExec_ret {Sigma A : Type} (a : A) (P : Sigma -> Prop)
    (X : A -> Sigma -> Prop) :
    safeExec P (ret a) X -> exists s, P s /\ X a s := by
  rintro ⟨s, hp, hs⟩
  exact ⟨s, hp, hs a s ⟨rfl, rfl⟩⟩

theorem safeExec_ret_tt {Sigma : Type} (P X : Sigma -> Prop) :
    safeExec P (ret ()) (fun _ => X) -> exists s, P s /\ X s :=
  safeExec_ret () P (fun _ => X)

theorem program_para_equiv {Sigma A B : Type}
    (f1 f2 : A -> program Sigma B) :
    Sets.equiv f1 f2 -> forall x, Sets.equiv (f1 x) (f2 x) := by
  exact fun h x => h x

theorem safeExec_result_state {Sigma A : Type} (P : Sigma -> Prop)
    (c : program Sigma A) :
    (exists s, P s) -> safeExec P c (result_state P c) := by
  rintro ⟨s, hp⟩
  exact ⟨s, hp, fun a s' hc => ⟨s, hp, hc⟩⟩

theorem Hoare_result_state {Sigma A : Type} (P : Sigma -> Prop)
    (c : program Sigma A) (Q : A -> Sigma -> Prop) :
    Hoare P c Q -> Sets.included (result_state P c) Q := by
  intro h a s'
  rintro ⟨s, hp, hc⟩
  exact h s a s' hp hc

theorem Hoare_safeexec_compose {Sigma A : Type} (P1 : Sigma -> Prop)
    (c : program Sigma A) (Q : A -> Sigma -> Prop) :
    Hoare P1 c Q -> forall (P2 : Sigma -> Prop) (a : A) (s : Sigma),
    safeExec P2 (ret a) (c s) -> P1 s -> exists s', Q a s' /\ P2 s' := by
  intro hh P2 a s
  rintro ⟨s', hp2, hs⟩ hp1
  have hc : c s a s' := hs a s' ⟨rfl, rfl⟩
  exact ⟨s', hh s a s' hp1 hc, hp2⟩

private theorem safeExec_bind_assoc_nf {Sigma A B C : Type}
    {c0 : program Sigma A} {c1 : A -> program Sigma B}
    {c2 : B -> program Sigma C} {P : Sigma -> Prop}
    {X : C -> Sigma -> Prop} :
    safeExec P (bind (bind c0 c1) c2) X ->
      safeExec P (bind c0 fun a => bind (c1 a) c2) X := by
  exact safeExec_proequiv _ _ _ _ (bind_assoc c0 c1 c2)

private theorem safeExec_bind_choice_nf {Sigma A B : Type}
    {c0 c1 : program Sigma A} {c2 : A -> program Sigma B}
    {P : Sigma -> Prop} {X : B -> Sigma -> Prop} :
    safeExec P (bind (choice c0 c1) c2) X ->
      safeExec P (choice (bind c0 c2) (bind c1 c2)) X := by
  exact safeExec_proequiv _ _ _ _ (bind_choice_equiv c0 c1 c2)

private theorem safeExec_bind_ret_left_nf {Sigma A B : Type}
    {a : A} {c : A -> program Sigma B} {P : Sigma -> Prop}
    {X : B -> Sigma -> Prop} :
    safeExec P (bind (ret a) c) X -> safeExec P (c a) X := by
  exact safeExec_proequiv _ _ _ _ (bind_ret_left a c)

private theorem safeExec_bind_ret_right_nf {Sigma A : Type}
    {c : program Sigma A} {P : Sigma -> Prop} {X : A -> Sigma -> Prop} :
    safeExec P (bind c ret) X -> safeExec P c X := by
  exact safeExec_proequiv _ _ _ _ (bind_ret_right c)

private theorem highstepbind_from_safe {Sigma A B : Type}
    {c1 : program Sigma A} {c2 : A -> program Sigma B}
    {P P' : Sigma -> Prop} {a : A} {X : B -> Sigma -> Prop} :
    safeExec P (bind c1 c2) X ->
    hs_eval c1 P P' a -> safeExec P' (c2 a) X := by
  intro hs he
  exact highstepbind_derive c1 c2 P a P' he X hs

syntax "state_prove_by_one_abs_step " term:max : tactic

namespace AbsStepTactic

open Lean Meta Elab Tactic

private def bindParts? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  let head := e.getAppFn
  if head.isConstOf ``StateRelMonad.bind || head.isConstOf ``MonadLib.bind then
    let args := e.getAppArgs
    if args.size >= 2 then
      some (args[args.size - 2]!, args[args.size - 1]!)
    else
      none
  else
    none

private def run (xSyntax : Syntax) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.getAppFn.isConstOf ``safeExec do
    throwError "state_prove_by_one_abs_step: expected a StateRelMonad.safeExec goal"
  let targetArgs := target.getAppArgs
  unless targetArgs.size >= 2 do
    throwError "state_prove_by_one_abs_step: malformed safeExec goal"
  let targetProgram := targetArgs[targetArgs.size - 2]!
  let targetPost := targetArgs[targetArgs.size - 1]!
  let mut candidate : Option (FVarId × Expr × Expr × Expr) := none
  for localDecl in (← getLCtx) do
    unless localDecl.isImplementationDetail do
      let type := (← instantiateMVars localDecl.type).consumeMData
      if type.getAppFn.isConstOf ``safeExec then
        let args := type.getAppArgs
        if args.size >= 2 then
          let sourceProgram := args[args.size - 2]!
          let sourcePost := args[args.size - 1]!
          if let some (c1, c2) := bindParts? sourceProgram then
            if ← isDefEq sourcePost targetPost then
              let sourcePre := args[args.size - 3]!
              candidate := some (localDecl.fvarId, c1, c2, sourcePre)
  let some (sourceHyp, c1, c2, sourcePre) := candidate |
    throwError "state_prove_by_one_abs_step: no matching safeExec/bind hypothesis"
  let c2Type ← whnf (← inferType c2)
  let .forallE _ argumentType _ _ := c2Type |
    throwError "state_prove_by_one_abs_step: malformed bind continuation"
  let x ← elabTerm xSyntax (some argumentType)
  unless ← isDefEq (mkApp c2 x) targetProgram do
    throwError "state_prove_by_one_abs_step: continuation at the supplied value does not match the goal"
  let sigma := targetArgs[0]!
  let resultType := targetArgs[1]!
  let targetPre := targetArgs[targetArgs.size - 3]!
  let sourceProof := mkFVar sourceHyp
  let rule ← mkAppOptM ``highstepbind_from_safe
    #[some sigma, some argumentType, some resultType, some c1, some c2,
      some sourcePre, some targetPre, some x, some targetPost, some sourceProof]
  let nextGoals ← goal.apply rule
  setGoals (← nextGoals.mapM fun nextGoal => nextGoal.tryClear sourceHyp)

end AbsStepTactic

elab_rules : tactic
  | `(tactic| state_prove_by_one_abs_step $x:term) => AbsStepTactic.run x

macro "state_abs_choice_left" : tactic =>
  `(tactic| (state_prog_nf; apply StateRelMonad.hsevalchoice_left_derive))

macro "state_abs_choice_right" : tactic =>
  `(tactic| (state_prog_nf; apply StateRelMonad.hsevalchoice_right_derive))

macro "state_abs_test_step" : tactic =>
  `(tactic|
    first
      | apply StateRelMonad.hsevaltest_derive
      | apply StateRelMonad.hsevaltestbind_derive)

macro "state_abs_ret_step" : tactic =>
  `(tactic| apply StateRelMonad.highret_eval2)

syntax "state_safe_step " ident : tactic
syntax "__state_safe_step_once " ident : tactic
syntax "__state_safe_prog_nf_once " ident : tactic
syntax "__state_safe_prog_nf " ident : tactic
syntax "__guard_state_safe " ident ident : tactic

namespace StateSafeTactic

open Lean Meta Elab Tactic

private def hasHead (e : Expr) (decl : Name) : Bool :=
  e.consumeMData.getAppFn.isConstOf decl

private def bindParts? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  if hasHead e ``StateRelMonad.bind || hasHead e ``MonadLib.bind then
    let args := e.getAppArgs
    if args.size >= 2 then
      some (args[args.size - 2]!, args[args.size - 1]!)
    else
      none
  else
    none

private def safeProgram (hyp : Lean.Syntax) : TacticM Expr := withMainContext do
  let fvarId <- getFVarId hyp
  let type <- instantiateMVars (← fvarId.getType)
  unless type.consumeMData.getAppFn.isConstOf ``safeExec do
    throwError "state safe tactic: expected a StateRelMonad.safeExec hypothesis"
  let args := type.getAppArgs
  unless args.size >= 2 do throwError "state safe tactic: malformed safeExec hypothesis"
  return args[args.size - 2]!

private def shapeMatches (kind : Name) (program : Expr) : Bool :=
  match kind with
  | `assoc =>
      match bindParts? program with
      | some (first, _) => (bindParts? first).isSome
      | none => false
  | `bindChoice =>
      match bindParts? program with
      | some (first, _) => hasHead first ``StateRelMonad.choice
      | none => false
  | `bindRetL =>
      match bindParts? program with
      | some (first, _) => hasHead first ``StateRelMonad.ret
      | none => false
  | `bindRetR =>
      match bindParts? program with
      | some (_, second) => hasHead second ``StateRelMonad.ret
      | none => false
  | `testPure =>
      match bindParts? program with
      | some (first, _) => hasHead first ``StateRelMonad.test'
      | none => false
  | `test =>
      match bindParts? program with
      | some (first, _) => hasHead first ``StateRelMonad.test
      | none => false
  | `choice => hasHead program ``StateRelMonad.choice
  | _ => false

elab_rules : tactic
  | `(tactic| __guard_state_safe $kind:ident $h:ident) => do
      let program <- safeProgram h
      unless shapeMatches kind.getId.eraseMacroScopes program do
        throwError "state safe tactic: hypothesis does not have the requested program shape"

end StateSafeTactic

macro_rules
  | `(tactic| __state_safe_prog_nf_once $h:ident) => do
      `(tactic|
        first
          | (__guard_state_safe assoc $h;
             replace $h := safeExec_bind_assoc_nf $h)
          | (__guard_state_safe bindChoice $h;
             replace $h := safeExec_bind_choice_nf $h)
          | (__guard_state_safe bindRetL $h;
             replace $h := safeExec_bind_ret_left_nf $h)
          | (__guard_state_safe bindRetR $h;
             replace $h := safeExec_bind_ret_right_nf $h))
  | `(tactic| __state_safe_prog_nf $h:ident) =>
      `(tactic| repeat __state_safe_prog_nf_once $h)
  | `(tactic| __state_safe_step_once $h:ident) => do
      `(tactic|
        first
          | (__guard_state_safe testPure $h;
             replace $h := StateRelMonad.safeExec_test_bind _ _ _ _
               (by first | trivial | assumption | simp_all) $h;
             __state_safe_prog_nf $h)
          | (__guard_state_safe test $h;
             replace $h := StateRelMonad.safeExec_testst_bind _ _ _ _
               (by intros; first | trivial | assumption | simp_all) $h;
             __state_safe_prog_nf $h))
  | `(tactic| state_safe_step $h:ident) => do
      `(tactic|
        (__state_safe_prog_nf $h;
         __state_safe_step_once $h;
         repeat __state_safe_step_once $h))

syntax "state_safe_choice_l " ident : tactic
macro_rules
  | `(tactic| state_safe_choice_l $h:ident) =>
      `(tactic|
        (__state_safe_prog_nf $h;
         __guard_state_safe choice $h;
         replace $h := StateRelMonad.safeExec_choice_l _ _ _ _ $h;
         __state_safe_prog_nf $h;
         repeat __state_safe_step_once $h))

syntax "state_safe_choice_r " ident : tactic
macro_rules
  | `(tactic| state_safe_choice_r $h:ident) =>
      `(tactic|
        (__state_safe_prog_nf $h;
         __guard_state_safe choice $h;
         replace $h := StateRelMonad.safeExec_choice_r _ _ _ _ $h;
         __state_safe_prog_nf $h;
         repeat __state_safe_step_once $h))

macro "state_safe_equiv" : tactic =>
  `(tactic|
    apply StateRelMonad.safeExec_proequiv <;>
      first | assumption | state_prog_nf)

end MonadLib.StateRelMonad
