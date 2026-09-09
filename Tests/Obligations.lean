import Graded.Obligations

/-! Examples instantiating every theorem of `Graded.Obligations` at the
    concrete error type `Graded.E`, plus the `Nat` counter-instance's own
    demonstration, and `#guard`/`decide` that `foldG`/`joinAllG` compute. -/

namespace Tests

open Graded List

-- ---------------------------------------------------------------------
-- All four classes resolve for `Grade E` — `IsCommPomonoid` and
-- `IsIdemPomonoid` as independent siblings, `IsCanonicalPomonoid` as the
-- bundle, per [obligation-layering]'s restructure.

example : Pomonoid (Grade E) := inferInstance
example : IsCommPomonoid (Grade E) := inferInstance
example : IsIdemPomonoid (Grade E) := inferInstance
example : IsCanonicalPomonoid (Grade E) := inferInstance

-- `foldG_le`/`foldG_cons_ne_nil`/`joinAllG_perm`, instantiated at `Grade E`.

example (xs : List Nat) : Pomonoid.le (foldG ({E.parse} : Grade E) xs) {E.parse} :=
  foldG_le {E.parse} xs

example (h : ([1, 2, 3] : List Nat) ≠ []) :
    foldG ({E.parse} : Grade E) [1, 2, 3] = ({E.parse} : Grade E) :=
  foldG_cons_ne_nil {E.parse} [1, 2, 3] h

example (gs gs' : List (Grade E)) (h : gs ~ gs') : joinAllG gs = joinAllG gs' :=
  joinAllG_perm h

-- `foldG`/`joinAllG` compute at `Grade E`.
#guard foldG ({E.parse} : Grade E) [1, 2, 3] = ({E.parse} : Grade E)
#guard joinAllG ([{E.parse}, {E.range}] : List (Grade E)) = {E.parse, E.range}
example : foldG ({E.parse} : Grade E) [1, 2, 3] = ({E.parse} : Grade E) := by decide

-- ---------------------------------------------------------------------
-- The `Nat` layers resolve, and neither `IsIdemPomonoid Nat` nor
-- `IsCanonicalPomonoid Nat` does (no `example : IsIdemPomonoid Nat :=
-- inferInstance` or `IsCanonicalPomonoid` analogue exists in this file,
-- because neither should typecheck) — `Nat` is commutative but not
-- idempotent, so it inhabits `IsCommPomonoid` alone, never the bundle.

example : Pomonoid Nat := inferInstance
example : IsCommPomonoid Nat := inferInstance

example : ¬ ∀ a : Nat, a + a = a := nat_not_idem

-- `foldG`/`joinAllG` compute at `Nat`, and disagree with the `Grade`
-- shape: the traversal grade grows, rather than staying put.
#guard foldG (1 : Nat) [(), (), ()] = 3
#guard joinAllG ([1, 2, 3] : List Nat) = 6

example (gs gs' : List Nat) (h : gs ~ gs') : joinAllG gs = joinAllG gs' :=
  joinAllG_perm h

end Tests
