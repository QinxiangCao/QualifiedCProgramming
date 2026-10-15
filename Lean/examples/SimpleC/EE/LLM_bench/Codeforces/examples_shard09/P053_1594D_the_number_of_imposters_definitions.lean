import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import AUXLib.ZParity

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
open AUXLib


open MaxMinLib
abbrev Comment := (Int × Int) × Int
abbrev _Prod__Prod_Z_Z_Z := Comment
abbrev fst {A B : Type} (p : A × B) : A := p.1
abbrev snd {A B : Type} (p : A × B) : B := p.2

def RolesConsistent (n : Int) (comments : List Comment) (roles : List Int) : Prop :=
  Zlength roles = n ∧ Forall (fun r => r = 0 ∨ r = 1) roles ∧ ∀ q, q ∈ comments →
    let ((i,j),c) := q
    (Znth (i-1) roles 0 = 0 ∧ Znth (j-1) roles 0 = c) ∨ (Znth (i-1) roles 0 = 1 ∧ Znth (j-1) roles 0 ≠ c)

def Pre (n : Int) (comments : List Comment) : Prop := True
def ImposterCount (roles : List Int) : Int := roles.foldr (· + ·) 0

def Spec (n : Int) (comments : List Comment) (out : Int) : Prop :=
  (out = -1 ∧ ¬ ∃ r, RolesConsistent n comments r) ∨
    (out ≥ 0 ∧ max_value_of_subset (· ≤ ·) (fun v => ∃ r, RolesConsistent n comments r ∧ v = ImposterCount r) (fun x => x) out)

def comment_at (comments : List Comment) (i : Int) : Comment := Znth i comments ((0,0),0)
def edge_src (comments : List Comment) (e : Int) : Int :=
  let ((u,v),_) := comment_at comments (Z.div e 2)
  if Z.even e then u else v

def edge_dst (comments : List Comment) (e : Int) : Int :=
  let ((u,v),_) := comment_at comments (Z.div e 2)
  if Z.even e then v else u

def edge_wt (comments : List Comment) (e : Int) : Int :=
  let ((_,_),w) := comment_at comments (Z.div e 2)
  w

inductive AdjChain (ns : List Int) : Int → List Int → Prop
  | adj_end : AdjChain ns (-1) []
  | adj_cons : ∀ e rest, 0 ≤ e → AdjChain ns (Znth e ns 0) rest → AdjChain ns e (e :: rest)
export AdjChain (adj_end adj_cons)

def ForwardStar (n cap k : Int) (hs ns ts ws : List Int) (comments : List Comment) : Prop :=
  Zlength hs = n+1 ∧ Zlength ns = 2*cap ∧ Zlength ts = 2*cap ∧ Zlength ws = 2*cap ∧
    (0 ≤ k ∧ k ≤ cap) ∧ k ≤ Zlength comments ∧
    (∀ e, (0 ≤ e ∧ e < 2*k) → Znth e ts 0 = edge_dst comments e ∧ Znth e ws 0 = edge_wt comments e) ∧
    (∀ u, (1 ≤ u ∧ u ≤ n) → ∃ es, AdjChain ns (Znth u hs 0) es ∧ es.Nodup ∧
      ∀ e, e ∈ es ↔ (0 ≤ e ∧ e < 2*k) ∧ edge_src comments e = u)

def ColourValues (n : Int) (cs : List Int) : Prop :=
  Zlength cs = n+1 ∧ ∀ v, (1 ≤ v ∧ v ≤ n) → Znth v cs 0 = -1 ∨ Znth v cs 0 = 0 ∨ Znth v cs 0 = 1

def ParityRespected (comments : List Comment) (cs : List Int) : Prop :=
  ∀ i, (0 ≤ i ∧ i < Zlength comments) →
    let ((u,v),w) := comment_at comments i
    Znth u cs 0 ≠ -1 → Znth v cs 0 ≠ -1 → Znth v cs 0 = Z.lxor (Znth u cs 0) w

def ColouredClosed (comments : List Comment) (cs : List Int) : Prop :=
  ∀ i, (0 ≤ i ∧ i < Zlength comments) →
    let ((u,v),_) := comment_at comments i
    Znth u cs 0 ≠ -1 ↔ Znth v cs 0 ≠ -1

def OnSet (n : Int) (cs r : List Int) : Prop :=
  Zlength r = n ∧
    (∀ v, (1 ≤ v ∧ v ≤ n) → Znth v cs 0 ≠ -1 → Znth (v-1) r 0 = 0 ∨ Znth (v-1) r 0 = 1) ∧
    (∀ v, (1 ≤ v ∧ v ≤ n) → Znth v cs 0 = -1 → Znth (v-1) r 0 = 0)

def ConsistentOn (n : Int) (comments : List Comment) (cs r : List Int) : Prop :=
  OnSet n cs r ∧ ∀ i, (0 ≤ i ∧ i < Zlength comments) →
    let ((u,v),w) := comment_at comments i
    Znth u cs 0 ≠ -1 → Znth v cs 0 ≠ -1 → Znth (v-1) r 0 = Z.lxor (Znth (u-1) r 0) w

def MaxImpostersOn (n : Int) (comments : List Comment) (cs : List Int) (t : Int) : Prop :=
  max_value_of_subset (· ≤ ·) (fun x => ∃ r, ConsistentOn n comments cs r ∧ x = r.foldr (· + ·) 0) (fun x => x) t

def HeadsInitialised (hs : List Int) (next : Int) : Prop := ∀ v, (1 ≤ v ∧ v < next) → Znth v hs 0 = -1
def ColoursInitialised (cs : List Int) (next : Int) : Prop := ∀ v, (1 ≤ v ∧ v < next) → Znth v cs 0 = -1

def ForwardStarRanges (n k : Int) (hs ns ts ws : List Int) : Prop :=
  (∀ u, (1 ≤ u ∧ u ≤ n) → (-1 ≤ Znth u hs 0 ∧ Znth u hs 0 < 2*k)) ∧
    (∀ e, (0 ≤ e ∧ e < 2*k) → (-1 ≤ Znth e ns 0 ∧ Znth e ns 0 < 2*k) ∧
      (1 ≤ Znth e ts 0 ∧ Znth e ts 0 ≤ n) ∧ (Znth e ws 0 = 0 ∨ Znth e ws 0 = 1))

def NewColourSet (n : Int) (before after vs : List Int) : Prop :=
  vs.Nodup ∧ Forall (fun v => 1 ≤ v ∧ v ≤ n) vs ∧
    (∀ v, (1 ≤ v ∧ v ≤ n) → (v ∈ vs ↔ Znth v before 0 = -1 ∧ Znth v after 0 ≠ -1)) ∧
    (∀ v, (1 ≤ v ∧ v ≤ n) → v ∉ vs → Znth v after 0 = Znth v before 0)

def ColourCount (cs vertices : List Int) (bit count : Int) : Prop :=
  count = ((vertices.map (fun v => Znth v cs 0)).count bit : Int)

def ComponentTwoChoices (n : Int) (comments : List Comment) (cs vertices : List Int) : Prop :=
  ∀ roles, RolesConsistent n comments roles → ∃ flip, (flip = 0 ∨ flip = 1) ∧
    ∀ v, v ∈ vertices → Znth (v-1) roles 0 = Z.lxor (Znth v cs 0) flip

def FullyScanned (comments : List Comment) (cs finished : List Int) : Prop :=
  ∀ e, (0 ≤ e ∧ e < 2 * Zlength comments) → edge_src comments e ∈ finished →
    Znth (edge_dst comments e) cs 0 ≠ -1 ∧ Znth (edge_dst comments e) cs 0 = Z.lxor (Znth (edge_src comments e) cs 0) (edge_wt comments e)

def ScanAt (comments : List Comment) (ns cs : List Int) (u cur : Int) : Prop :=
  ∃ remaining, AdjChain ns cur remaining ∧
    (∀ e, (0 ≤ e ∧ e < 2 * Zlength comments) → edge_src comments e = u → e ∉ remaining →
      Znth (edge_dst comments e) cs 0 ≠ -1 ∧ Znth (edge_dst comments e) cs 0 = Z.lxor (Znth u cs 0) (edge_wt comments e))

def ComponentFrontier (n : Int) (comments : List Comment) (before after finished pending : List Int) (c0 c1 : Int) : Prop :=
  ColourValues n after ∧ NewColourSet n before after (finished ++ pending) ∧
    ComponentTwoChoices n comments after (finished ++ pending) ∧ FullyScanned comments after finished ∧
    ColourCount after finished 0 c0 ∧ ColourCount after finished 1 c1

def ComponentScan (n : Int) (comments : List Comment) (ns before after finished pending : List Int) (u cur c0 c1 : Int) : Prop :=
  ColourValues n after ∧ NewColourSet n before after (finished ++ u :: pending) ∧
    ComponentTwoChoices n comments after (finished ++ u :: pending) ∧ FullyScanned comments after finished ∧
    ScanAt comments ns after u cur ∧ ColourCount after (finished ++ [u]) 0 c0 ∧ ColourCount after (finished ++ [u]) 1 c1

def ComponentComplete (n : Int) (comments : List Comment) (before after vertices : List Int) (c0 c1 : Int) : Prop :=
  ComponentFrontier n comments before after vertices [] c0 c1 ∧ ParityRespected comments after ∧ ColouredClosed comments after ∧
    (∀ t, MaxImpostersOn n comments before t → MaxImpostersOn n comments after (t + max c0 c1))

def RolesConsistentOnVertices (n : Int) (comments : List Comment) (vertices roles : List Int) : Prop :=
  Zlength roles = n ∧ (∀ v, v ∈ vertices → Znth (v-1) roles 0 = 0 ∨ Znth (v-1) roles 0 = 1) ∧
    (∀ i, (0 ≤ i ∧ i < Zlength comments) →
      let ((u,v),w) := comment_at comments i
      u ∈ vertices → v ∈ vertices → Znth (v-1) roles 0 = Z.lxor (Znth (u-1) roles 0) w)

def ComponentTwoChoicesLocal (n : Int) (comments : List Comment) (cs vertices : List Int) : Prop :=
  ∀ roles, RolesConsistentOnVertices n comments vertices roles → ∃ flip, (flip = 0 ∨ flip = 1) ∧
    ∀ v, v ∈ vertices → Znth (v-1) roles 0 = Z.lxor (Znth v cs 0) flip

def ScanAtOwned (comments : List Comment) (ns cs : List Int) (u cur : Int) : Prop :=
  ScanAt comments ns cs u cur ∧ ∃ remaining, AdjChain ns cur remaining ∧ ∀ e, e ∈ remaining → edge_src comments e = u

def ComponentFrontierStrong (n : Int) (comments : List Comment) (before after finished pending : List Int) (c0 c1 : Int) : Prop :=
  ComponentFrontier n comments before after finished pending c0 c1 ∧ ComponentTwoChoicesLocal n comments after (finished ++ pending)

def ComponentScanStrong (n : Int) (comments : List Comment) (ns before after finished pending : List Int) (u cur c0 c1 : Int) : Prop :=
  ComponentScan n comments ns before after finished pending u cur c0 c1 ∧ ScanAtOwned comments ns after u cur ∧
    ComponentTwoChoicesLocal n comments after (finished ++ u :: pending)

def ComponentCompleteStrong (n : Int) (comments : List Comment) (before after vertices : List Int) (c0 c1 : Int) : Prop :=
  ComponentComplete n comments before after vertices c0 c1 ∧ ComponentTwoChoicesLocal n comments after vertices

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
