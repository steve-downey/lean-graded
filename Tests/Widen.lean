import Graded.Widen
import Examples.Validation

/-! Examples instantiating every `Graded.Widen` theorem at a concrete
    error type, plus a `#guard` that computes via `decide`. -/

namespace Tests

open Graded Examples.Validation

example (x : Graded ({E.parse} : Grade E) Nat) :
    widen (Grade.le_refl' _) x = x :=
  widen_refl x

example (h₁ : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (h₂ : ({E.parse, E.range} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E))
    (x : Graded ({E.parse} : Grade E) Nat) :
    widen h₂ (widen h₁ x) = widen (Grade.le_trans' h₁ h₂) x :=
  widen_widen h₁ h₂ x

example (h : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E)) (f : Nat → Nat)
    (x : Graded ({E.parse} : Grade E) Nat) :
    widen h (map f x) = map f (widen h x) :=
  widen_map h f x

example (h h' : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (x : Graded ({E.parse} : Grade E) Nat) :
    widen h x = widen h' x :=
  widen_irrel h h' x

example (e : ({E.parse, E.range} : Grade E) = ({E.range, E.parse} : Grade E))
    (h : ({E.range, E.parse} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E))
    (x : Graded ({E.parse, E.range} : Grade E) Nat) :
    widen h (cast e x) = widen (e ▸ h) x :=
  widen_cast e h x

example : (fromEmpty (3 : Nat) : Graded ({E.parse} : Grade E) Nat) = .ok 3 :=
  fromEmpty_eq_ok 3

#guard
  widen (Grade.le_refl' ({E.parse} : Grade E))
      (.ok 3 : Graded ({E.parse} : Grade E) Nat) =
    (.ok 3 : Graded ({E.parse} : Grade E) Nat)

end Tests
