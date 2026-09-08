import Graded.Carrier
import Examples.Validation

/-! Examples instantiating every `Graded.Carrier` theorem at a concrete
    error type, plus a `#guard` that computes via `decide`/`rfl`. -/

namespace Tests

open Graded Examples.Validation

example (x : Graded ({E.parse} : Grade E) Nat) :
    Graded.map (@id Nat) x = x :=
  Graded.map_id x

example (f : Nat → Nat) (h : Nat → Bool) (x : Graded ({E.parse} : Grade E) Nat) :
    Graded.map (h ∘ f) x = Graded.map h (Graded.map f x) :=
  Graded.map_comp f h x

example : Graded.emptyEquiv (Graded.ok (3 : Nat) : Graded (Grade.bot : Grade E) Nat) = 3 := by
  decide

example : Graded.emptyEquiv.symm (3 : Nat) =
    (Graded.ok (3 : Nat) : Graded (Grade.bot : Grade E) Nat) := by
  decide

#guard render (validate "42") = "ok 42"
#guard render (validate "abc") = "err Examples.Validation.E.parse"
#guard render (validate "9999") = "err Examples.Validation.E.range"

end Tests
