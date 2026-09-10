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

-- ---------------------------------------------------------------------
-- `cast_cast`: composing two transports. Instantiated across **three
-- different spellings of one grade** — the computed union, the literal
-- pair, and the pair written the other way round — so neither cast is
-- `cast rfl` and the composite is a genuine transport. A reflexive
-- instantiation would hold of a broken `cast`.

private theorem hUnion :
    Grade.join ({E.parse} : Grade E) {E.range} = ({E.parse, E.range} : Grade E) := by decide

private theorem hSwap :
    ({E.parse, E.range} : Grade E) = ({E.range, E.parse} : Grade E) := by decide

example (x : Graded (Grade.join ({E.parse} : Grade E) {E.range}) Nat) :
    Graded.cast hSwap (Graded.cast hUnion x) = Graded.cast (hUnion.trans hSwap) x :=
  Graded.cast_cast hUnion hSwap x

-- `map_emptyEquiv`: `map` at the empty grade agrees with applying the
-- function to the bare value the ∅-collapse hands back.
example (f : Nat → Nat) (x : Graded (Grade.bot : Grade E) Nat) :
    emptyEquiv (Graded.map f x) = f (emptyEquiv x) :=
  map_emptyEquiv f x

-- ---------------------------------------------------------------------
-- The payload carrier underneath, and the constructor behaviour the
-- specialization has to supply by hand. An `inductive` gives `simp`
-- injectivity and disjointness for free; `Graded.ok`/`Graded.err` are
-- `def`s over `ExpectedG`, so these four are stated rather than derived.

example (x y : Graded ({E.parse} : Grade E) Nat)
    (h : ExpectedG.toSum x = ExpectedG.toSum y) : x = y :=
  ExpectedG.toSum_inj h

example (a b : Nat) :
    (Graded.ok a : Graded ({E.parse} : Grade E) Nat) = Graded.ok b ↔ a = b :=
  Graded.ok_eq_ok

example (he he' : E.parse ∈ ({E.parse, E.range} : Grade E)) :
    (Graded.err E.parse he : Graded ({E.parse, E.range} : Grade E) Nat)
      = Graded.err E.parse he' ↔ E.parse = E.parse :=
  Graded.err_eq_err

example (a : Nat) (he : E.parse ∈ ({E.parse} : Grade E)) :
    (Graded.ok a : Graded ({E.parse} : Grade E) Nat) ≠ Graded.err E.parse he :=
  Graded.ok_ne_err

example (a : Nat) (he : E.parse ∈ ({E.parse} : Grade E)) :
    (Graded.err E.parse he : Graded ({E.parse} : Grade E) Nat) ≠ Graded.ok a :=
  Graded.err_ne_ok

-- Equality still decides and still computes, which is what every `#guard`
-- in this repository depends on.
#guard (Graded.ok 3 : Graded ({E.parse} : Grade E) Nat) = Graded.ok 3
#guard (Graded.ok 3 : Graded ({E.parse} : Grade E) Nat)
  ≠ Graded.err E.parse (by decide)

end Tests
