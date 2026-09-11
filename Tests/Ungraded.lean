import Graded.Ungraded
import Graded.Compose
import Examples.Validation

/-! Examples instantiating every named law in `Graded.Ungraded` at a
    concrete error type, plus a `#guard` that `bindF`/`apF` compute, and —
    the row [ungraded-baseline]'s §4 asks for — the flattened composition
    law re-checked at a single fixed grade: it fails here exactly as it
    fails in general ([compose-flatten]), confirming with `#guard` (not
    merely asserting) that the failure is not a fact about grading. -/

namespace Tests

open Graded Examples.Validation

/-- The one fixed grade every example below shares: two error kinds, so
    the flattened-composition counterexample has somewhere to disagree. -/
abbrev gE : Grade E := {E.parse, E.range}

/-- Render a `Fixed`-grade `Nat` result, for `#guard`. -/
def renderF : Fixed gE Nat → String
  | .ok n => s!"ok {n}"
  | .err e _ => s!"err {repr e}"

-- ---------------------------------------------------------------------
-- `bindF`: the ordinary monad laws, no grade arithmetic in sight.

example (a : Nat) (f : Nat → Fixed gE Nat) : bindF (pureF a : Fixed gE Nat) f = f a :=
  bindF_pure_left a f

example (x : Fixed gE Nat) : bindF x (pureF : Nat → Fixed gE Nat) = x :=
  bindF_pure_right x

example (x : Fixed gE Nat) (f : Nat → Fixed gE Nat) (k : Nat → Fixed gE Nat) :
    bindF (bindF x f) k = bindF x (fun a => bindF (f a) k) :=
  bindF_assoc x f k

-- `bindF` computes.
#guard renderF (bindF (pureF 41 : Fixed gE Nat) (fun n => pureF (n + 1))) = "ok 42"
#guard renderF (bindF (Graded.err E.parse (by decide) : Fixed gE Nat)
    (fun n => pureF (n + 1))) = "err Examples.Validation.E.parse"

-- ---------------------------------------------------------------------
-- `apF`: the ordinary applicative laws, no grade arithmetic in sight.

example (x : Fixed gE Nat) : apF (pureF (@id Nat) : Fixed gE (Nat → Nat)) x = x :=
  apF_pure_id x

example (f : Nat → Nat) (a : Nat) :
    apF (pureF f : Fixed gE (Nat → Nat)) (pureF a : Fixed gE Nat) = (pureF (f a) : Fixed gE Nat) :=
  apF_pure_pure f a

example (u : Fixed gE (Nat → Nat)) (a : Nat) :
    apF u (pureF a : Fixed gE Nat) =
      apF (pureF (fun f => f a) : Fixed gE ((Nat → Nat) → Nat)) u :=
  apF_interchange u a

example (u : Fixed gE (Nat → Nat)) (v : Fixed gE (Nat → Nat)) (w : Fixed gE Nat) :
    apF (apF (apF (pureF Function.comp :
        Fixed gE ((Nat → Nat) → (Nat → Nat) → Nat → Nat)) u) v) w = apF u (apF v w) :=
  apF_comp u v w

-- `apF` computes.
#guard renderF (apF (pureF (· + 1) : Fixed gE (Nat → Nat)) (pureF 41 : Fixed gE Nat)) = "ok 42"

-- ---------------------------------------------------------------------
-- The Mathlib correspondence.

example (a : Nat) : sumEquiv (pureF a : Fixed gE Nat) = Sum.inr a :=
  sumEquiv_pureF a

example (x : Fixed gE Nat) (f : Nat → Fixed gE Nat) :
    sumEquiv (bindF x f) = Sum.bind (sumEquiv x) (fun a => sumEquiv (f a)) :=
  sumEquiv_bindF x f

-- `sumEquiv` computes, both directions.
#guard sumEquiv (pureF 42 : Fixed gE Nat) = Sum.inr 42
#guard sumEquiv.symm (Sum.inr 42 : {e : E // e ∈ gE} ⊕ Nat) = (pureF 42 : Fixed gE Nat)

-- `traverse` needs no fixed-grade specialization; the one new fact is
-- the Mathlib correspondence `traverse_fromEmpty_map`.
example (f : Nat → Nat) (xs : List Nat) :
    traverse (fromEmpty ∘ f : Nat → Graded gE Nat) xs = fromEmpty (xs.map f) :=
  traverse_fromEmpty_map f xs

-- ---------------------------------------------------------------------
-- §4: the flattened composition law, re-checked at this one fixed grade.
-- `fT` fails (with `E.parse`) at the *later* position 1; `kT` fails (with
-- `E.range`) at the *earlier* position 0. `flatten (map (traverse kT)
-- (traverse fT xs))` runs every position's `fT` before any `kT`, so
-- position 1's `E.parse` is the only failure it ever sees; `traverse (fun
-- a => flatten (map kT (fT a))) xs` combines `fT`/`kT` per position before
-- traversing, so its own left-to-right short circuit reports position 0's
-- `E.range` first. Both are legitimate values the definitions compute —
-- confirmed below, not asserted — and they disagree: the same
-- counterexample [compose-flatten] found survives with `f` and `k` fixed
-- to the *same* grade, so the failure was never a fact about grading.

def fT : Nat → Graded gE Nat
  | 0 => .ok 0
  | _ => .err E.parse (by decide)

def kT : Nat → Graded gE Nat
  | 0 => .err E.range (by decide)
  | n => .ok n

def renderFlat : Graded (Grade.join gE gE) (List Nat) → String
  | .ok l => s!"ok {l}"
  | .err e _ => s!"err {repr e}"

#guard renderFlat (flatten (map (traverse kT) (traverse fT [0, 1]))) =
  "err Examples.Validation.E.parse"
#guard renderFlat (traverse (fun a => flatten (map kT (fT a))) [0, 1]) =
  "err Examples.Validation.E.range"

-- ---------------------------------------------------------------------
-- The six fixed-grade reduction lemmas. The grade here is deliberately
-- `{parse, range}` rather than a singleton: `apF` collapses
-- `Grade.join g g` back to `g` with `Grade.join_idem`, and a two-element
-- grade makes that collapse a real one rather than a coincidence about
-- singletons.

example (a : Nat) : (pureF a : Fixed ({E.parse, E.range} : Grade E) Nat) = Graded.ok a :=
  pureF_eq_ok a

example (a : Nat) (f : Nat → Fixed ({E.parse, E.range} : Grade E) Nat) :
    bindF (Graded.ok a : Fixed ({E.parse, E.range} : Grade E) Nat) f = f a :=
  bindF_ok a f

example (he : E.parse ∈ ({E.parse, E.range} : Grade E))
    (f : Nat → Fixed ({E.parse, E.range} : Grade E) Nat) :
    bindF (Graded.err E.parse he : Fixed ({E.parse, E.range} : Grade E) Nat) f
      = Graded.err E.parse he :=
  bindF_err E.parse he f

example (f : Nat → Nat) (a : Nat) :
    apF (Graded.ok f : Fixed ({E.parse, E.range} : Grade E) (Nat → Nat))
        (Graded.ok a : Fixed ({E.parse, E.range} : Grade E) Nat) = Graded.ok (f a) :=
  apF_ok_ok f a

example (he : E.parse ∈ ({E.parse, E.range} : Grade E))
    (x : Fixed ({E.parse, E.range} : Grade E) Nat) :
    apF (Graded.err E.parse he : Fixed ({E.parse, E.range} : Grade E) (Nat → Nat)) x
      = Graded.err E.parse he :=
  apF_err_left E.parse he x

-- The two error sides use *distinguishable* kinds, so this is not the
-- previous example with the arguments swapped.
example (f : Nat → Nat) (he : E.range ∈ ({E.parse, E.range} : Grade E)) :
    apF (Graded.ok f : Fixed ({E.parse, E.range} : Grade E) (Nat → Nat))
        (Graded.err E.range he : Fixed ({E.parse, E.range} : Grade E) Nat)
      = Graded.err E.range he :=
  apF_ok_err f E.range he

end Tests
