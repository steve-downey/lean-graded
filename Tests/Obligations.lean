import Graded.Obligations

/-! Examples instantiating every theorem of `Graded.Obligations` at the
    concrete error type `Graded.E`, plus the `Nat` counter-instance's own
    demonstration, and `#guard`/`decide` that `foldG`/`joinAllG` compute. -/

namespace Tests

open Graded List

-- ---------------------------------------------------------------------
-- The three layers resolve for `Grade E`.

example : Pomonoid (Grade E) := inferInstance
example : IsCommPomonoid (Grade E) := inferInstance
example : IsIdemPomonoid (Grade E) := inferInstance

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
-- The `Nat` layers resolve, and `IsIdemPomonoid Nat` deliberately does not
-- (no `example : IsIdemPomonoid Nat := inferInstance` exists in this file,
-- because none should typecheck).

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
