import SimpleC.SL.SeparationLogic

/-! Annotation-facing interfaces whose names or argument order differ from
Lean's standard library. Equality, comparisons, map and concat are printed
using their standard Lean declarations and need no duplicate definitions. -/

namespace AUXLib

abbrev hd {A : Type u} (fallback : A) (xs : List A) : A := xs.headD fallback

export SimpleC.SL.ArrayLibCore.ArrayLibCoreSig (repeat_Z)

end AUXLib

namespace ListLib

abbrev sum (xs : List Int) : Int := AUXLib.sum xs

end ListLib
