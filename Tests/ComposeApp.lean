import Graded.ComposeApp
import Examples.Validation

/-! Examples instantiating every `Graded.ComposeApp` theorem at a concrete
    error type, plus `#guard`s that `Comp.ap`/`traverseComp`/`flatten_ap`
    compute and not just typecheck. `#guard` on a `Comp g h α` value is
    routed through `String`, doubled: render the outer shape, and for an
    outer `ok`, render the inner shape too — the same detour every
    consumer since [monad-laws] has needed for a single `Graded`, now
    nested. -/

namespace Tests

open Graded Examples.Validation

/-- Render a `Comp g h Nat` result for `#guard`/`#eval`, at any grade pair. -/
def renderComp {g h : Grade E} : Comp g h Nat → String
  | .ok (.ok n) => s!"ok (ok {n})"
  | .ok (.err e _) => s!"ok (err {repr e})"
  | .err e _ => s!"err {repr e}"

/-- Render a `Comp g h (List Nat)` result, for `traverseComp`. -/
def renderCompList {g h : Grade E} : Comp g h (List Nat) → String
  | .ok (.ok ns) => s!"ok (ok {ns})"
  | .ok (.err e _) => s!"ok (err {repr e})"
  | .err e _ => s!"err {repr e}"

-- ---------------------------------------------------------------------
-- The functor laws.

example (x : Comp ({E.parse} : Grade E) ({E.range} : Grade E) Nat) :
    Comp.map (@id Nat) x = x :=
  Comp.map_id x

example (x : Comp ({E.parse} : Grade E) ({E.range} : Grade E) Nat) :
    Comp.map ((· + 1) ∘ (· * 2)) x = Comp.map (· + 1) (Comp.map (· * 2) x) :=
  Comp.map_comp (· * 2) (· + 1) x

-- ---------------------------------------------------------------------
-- The four applicative laws, each at concrete grades.

example (x : Comp ({E.parse} : Grade E) ({E.range} : Grade E) Nat) :
    Comp.castGH (Grade.bot_join _) (Grade.bot_join _)
        (Comp.ap (Comp.pure (@id Nat) :
          Comp (Grade.bot : Grade E) Grade.bot (Nat → Nat)) x) = x :=
  Comp.ap_pure_id x

example (f : Nat → Nat) (a : Nat) :
    Comp.castGH (Grade.bot_join (Grade.bot : Grade E)) (Grade.bot_join (Grade.bot : Grade E))
        (Comp.ap (Comp.pure f : Comp (Grade.bot : Grade E) Grade.bot (Nat → Nat))
          (Comp.pure a)) =
      Comp.pure (f a) :=
  Comp.ap_pure_pure f a

example (u : Comp ({E.parse} : Grade E) ({E.range} : Grade E) (Nat → Nat)) (a : Nat) :
    Comp.castGH (Grade.join_bot _) (Grade.join_bot _) (Comp.ap u (Comp.pure a)) =
      Comp.castGH (Grade.bot_join _) (Grade.bot_join _)
        (Comp.ap (Comp.pure (fun f => f a) :
          Comp (Grade.bot : Grade E) Grade.bot ((Nat → Nat) → Nat)) u) :=
  Comp.ap_interchange u a

example (u : Comp ({E.parse} : Grade E) ({E.range} : Grade E) (Nat → Nat))
    (v : Comp ({E.range} : Grade E) ({E.io} : Grade E) (Nat → Nat))
    (w : Comp ({E.io} : Grade E) ({E.parse} : Grade E) Nat) :
    Comp.castGH
        (by rw [Grade.bot_join, Grade.join_assoc] :
          Grade.join (Grade.join (Grade.join (Grade.bot : Grade E) {E.parse}) {E.range}) {E.io} =
            Grade.join {E.parse} (Grade.join {E.range} {E.io}))
        (by rw [Grade.bot_join, Grade.join_assoc] :
          Grade.join (Grade.join (Grade.join (Grade.bot : Grade E) {E.range}) {E.io}) {E.parse} =
            Grade.join {E.range} (Grade.join {E.io} {E.parse}))
        (Comp.ap (Comp.ap (Comp.ap
            (Comp.pure Function.comp :
              Comp (Grade.bot : Grade E) Grade.bot ((Nat → Nat) → (Nat → Nat) → Nat → Nat))
            u) v) w) =
      Comp.ap u (Comp.ap v w) :=
  Comp.ap_comp u v w

-- `Comp.ap` computes.
#guard renderComp (Comp.ap
    (Graded.ok (Graded.ok (· + 1)) : Comp ({E.parse} : Grade E) ({E.range} : Grade E) (Nat → Nat))
    (Graded.ok (Graded.ok 41) : Comp ({E.io} : Grade E) ({E.parse} : Grade E) Nat)) = "ok (ok 42)"

-- ---------------------------------------------------------------------
-- `traverseComp_eq`: the composition law, unflattened. `parseNat` (grade
-- `{E.parse}`) supplies the outer layer, `checkRange`-wrapped-as-a-second-
-- stage-that-cannot-itself-fail supplies the inner. Concretely: traverse a
-- list with `f := parseNat`, then `k := fun n => checkRange n` layered on
-- top via `map`, and compare the composed traversal against
-- `map (traverse checkRange) (traverse parseNat xs)`.

example (xs : List String) :
    traverseComp (fun a => Graded.map checkRange (parseNat a)) xs =
      Graded.map (traverse checkRange) (traverse parseNat xs) :=
  traverseComp_eq parseNat checkRange xs

-- `traverseComp` computes, uniformly at grade `({E.parse}, {E.range})`
-- regardless of the list's length — the same length-independence
-- `traverse` itself has, now for the *composed* traversal.
#guard renderCompList (traverseComp (fun a => Graded.map checkRange (parseNat a)) ["1", "2", "3"])
  = "ok (ok [1, 2, 3])"

-- A failure in the *inner* stage (`checkRange`) surfaces as an inner
-- `err`, the outer layer still `ok` (the parse itself succeeded).
#guard renderCompList
    (traverseComp (fun a => Graded.map checkRange (parseNat a)) ["1", "9999", "3"])
  = "ok (err Examples.Validation.E.range)"

-- A failure in the *outer* stage (`parseNat`) surfaces as an outer `err`,
-- and short-circuits before the inner stage is ever consulted.
#guard renderCompList (traverseComp (fun a => Graded.map checkRange (parseNat a)) ["1", "x", "3"])
  = "err Examples.Validation.E.parse"

-- The same computation, via the two sides of `traverseComp_eq` directly:
-- both must render identically, since the theorem says they are equal.
#guard renderCompList (traverseComp (fun a => Graded.map checkRange (parseNat a)) ["1", "2", "3"])
  = renderCompList (Graded.map (traverse checkRange) (traverse parseNat ["1", "2", "3"]))

-- ---------------------------------------------------------------------
-- `flatten_ap`, at the concrete grades where its hypothesis is trivially
-- satisfied (`xx`'s outer layer is `ok`).

example (ff : Comp ({E.parse} : Grade E) ({E.range} : Grade E) (Nat → Nat)) (a : Nat) :
    flatten (Comp.ap ff (Comp.pure a :
        Comp (Grade.bot : Grade E) Grade.bot Nat)) =
      Graded.cast (Comp.grade_reassoc _ _ _ _) (ap (flatten ff) (flatten (Comp.pure a))) :=
  flatten_ap ff (Comp.pure a) (Or.inr (Or.inr ⟨Graded.ok a, rfl⟩))

-- The same law at four *non-empty, distinct* grades, so that
-- `Comp.grade_reassoc`'s equation does not collapse by the unit laws
-- alone. In the instance above `xx` sits at `∅`/`∅`, which makes
-- `(g ⊔ h) ⊔ (∅ ⊔ ∅) = (g ⊔ ∅) ⊔ (h ⊔ ∅)` a consequence of `bot_join`
-- and `join_bot`; commutativity is never reached. Here every one of the
-- four grades is inhabited, so the reassociation genuinely needs
-- `Grade.join_comm`, which `grade_reassoc` cites. This is the model's
-- commutativity path under test rather than merely stated.

example (ff : Comp ({E.parse} : Grade E) ({E.range} : Grade E) (Nat → Nat)) :
    flatten (Comp.ap ff (Graded.ok (Graded.ok 1) :
        Comp ({E.io} : Grade E) ({E.parse} : Grade E) Nat)) =
      Graded.cast (Comp.grade_reassoc _ _ _ _)
        (ap (flatten ff) (flatten (Graded.ok (Graded.ok 1) :
          Comp ({E.io} : Grade E) ({E.parse} : Grade E) Nat))) :=
  flatten_ap ff (Graded.ok (Graded.ok 1)) (Or.inr (Or.inr ⟨Graded.ok 1, rfl⟩))

end Tests
