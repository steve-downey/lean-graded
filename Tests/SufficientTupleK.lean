import Graded.Sufficient.TupleK
import Examples.Validation

/-! Examples for `Graded.sequenceK`, the sufficient-grade sibling
    heterogeneous sequencing had been missing. Fixtures are genuinely
    heterogeneous — two distinct payload types at two distinct grades,
    nominated into a third grade strictly containing both — since a
    homogeneous pair, or a nominated grade equal to the fold, would pass
    against an implementation that ignored an index. -/

namespace Tests.SufficientTupleK

open Graded Examples.Validation List

abbrev KT : Grade E := {E.parse, E.range, E.io}

theorem hslots : ∀ g ∈ ([{E.parse}, {E.range}] : List (Grade E)), g ⊆ KT := by decide

def pairK : GList ([{E.parse}, {E.range}] : List (Grade E)) [Nat, String] :=
  GList.cons (Graded.ok 7) (GList.cons (Graded.ok "hi") GList.nil)

def badK : GList ([{E.parse}, {E.range}] : List (Grade E)) [Nat, String] :=
  GList.cons (Graded.err E.parse (by decide)) (GList.cons (Graded.ok "hi") GList.nil)

def renderK : Graded KT (HList [Nat, String]) → String
  | .ok (n, s, _) => s!"ok ({n}, {s})"
  | .err e _ => s!"err {repr e}"

-- The result lands at the nominated grade for every tuple, with no fold
-- of the slot grades appearing in the type.
#guard renderK (sequenceK hslots pairK) = "ok (7, hi)"
#guard renderK (sequenceK hslots badK) = "err Examples.Validation.E.parse"

example : sequenceK (k := KT) (fun _ h => absurd h (by simp))
    (GList.nil : GList [] ([] : List (Type))) = pureK HList.nil :=
  sequenceK_nil _

example (g : Grade E) (gs : List (Grade E)) (β : Type) (αs : List Type)
    (h : ∀ g' ∈ g :: gs, g' ⊆ KT) (x : Graded g β) (xs : GList gs αs) :
    sequenceK h (GList.cons x xs)
      = map2K (h g List.mem_cons_self) (Grade.le_refl' KT) HList.cons x
          (sequenceK (fun g' hg' => h g' (List.mem_cons_of_mem g hg')) xs) :=
  sequenceK_cons h x xs

-- Which witness justifies each slot does not matter, only that one
-- exists — and here that is a whole family of witnesses, not one.
example (h h' : ∀ g ∈ ([{E.parse}, {E.range}] : List (Grade E)), g ⊆ KT) :
    sequenceK h pairK = sequenceK h' pairK :=
  sequenceK_irrel h h' pairK

end Tests.SufficientTupleK
