import Graded.Obligations

/-! Examples instantiating every theorem of `Graded.Obligations` at the
    concrete error type `Graded.E`, plus the `Nat` counter-instance's own
    demonstration, and `#guard`/`decide` that `foldG`/`joinAllG` compute. -/

namespace Tests

open Graded List

-- ---------------------------------------------------------------------
-- Every class resolves for `Grade E`: the base algebra, and all four
-- mixins as independent `Prop` classes over the one base instance. The
-- bundle is now the conjunction rather than a class of its own.

example : PreorderedGradeMonoid (Grade E) := inferInstance
example : IsCommGrade (Grade E) := inferInstance
example : IsIdemGrade (Grade E) := inferInstance
example : IsLubGrade (Grade E) := inferInstance
example : IsPartialOrderGrade (Grade E) := inferInstance
example : IsCanonicalGrade (Grade E) := grade_isCanonical

-- The two lifts between `IsLubGrade` and `IsIdemGrade`, instantiated.
-- Both are theorems rather than instances, so they have to be applied by
-- name — which is the point: `Grade E` already has both classes
-- directly, and neither lift is allowed to become a second route.

example : IsLubGrade (Grade E) := IsLubGrade.of_idem
example : IsIdemGrade (Grade E) := IsIdemGrade.of_lub_of_antisymm

example (g : Grade E) :
    PreorderedGradeMonoid.le (PreorderedGradeMonoid.join g g) g ∧
      PreorderedGradeMonoid.le g (PreorderedGradeMonoid.join g g) :=
  join_self_equiv g

example {g h k : Grade E} (hg : PreorderedGradeMonoid.le g k)
    (hh : PreorderedGradeMonoid.le h k) :
    PreorderedGradeMonoid.le (PreorderedGradeMonoid.join g h) k :=
  join_le hg hh

-- `foldG_le`/`foldG_cons_ne_nil`/`joinAllG_perm`, instantiated at `Grade E`.

example (xs : List Nat) : PreorderedGradeMonoid.le (foldG ({E.parse} : Grade E) xs) {E.parse} :=
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
-- The `Nat` layers resolve. No `IsIdemGrade Nat` and no `IsLubGrade Nat`
-- example appears in this file, because neither should typecheck: `Nat`
-- is commutative and antisymmetric, and is neither idempotent nor a
-- least upper bound.

example : PreorderedGradeMonoid Nat := inferInstance
example : IsCommGrade Nat := inferInstance
example : IsPartialOrderGrade Nat := inferInstance

example : ¬ ∀ a : Nat, a + a = a := nat_not_idem

-- `foldG`/`joinAllG` compute at `Nat`, and disagree with the `Grade`
-- shape: the traversal grade grows, rather than staying put.
#guard foldG (1 : Nat) [(), (), ()] = 3
#guard joinAllG ([1, 2, 3] : List Nat) = 6

example (gs gs' : List Nat) (h : gs ~ gs') : joinAllG gs = joinAllG gs' :=
  joinAllG_perm h

-- ---------------------------------------------------------------------
-- The pack: the base class and `IsLubGrade` resolve, and the three laws
-- canonicalization exists to supply are refuted. No `IsPartialOrderGrade
-- (Pack E)`, `IsCommGrade (Pack E)` or `IsIdemGrade (Pack E)` example
-- appears here, because none should typecheck.

example : PreorderedGradeMonoid (Pack E) := inferInstance
example : IsLubGrade (Pack E) := inferInstance

example : ¬ IsPartialOrderGrade (Pack E) := pack_not_antisymm
example : ¬ IsIdemGrade (Pack E) := pack_not_idem
example : ¬ IsCommGrade (Pack E) := pack_not_comm

-- What the pack does have, from `IsLubGrade` alone: the two-way order
-- fact that `pack_not_idem` refuses to close into an equality.
example (g : Pack E) :
    PreorderedGradeMonoid.le (PreorderedGradeMonoid.join g g) g ∧
      PreorderedGradeMonoid.le g (PreorderedGradeMonoid.join g g) :=
  join_self_equiv g

-- The pack computes, and disagrees with `Grade` on both spellings.
#guard ([E.parse] ++ [E.parse] : Pack E) = [E.parse, E.parse]
#guard ([E.parse] ++ [E.range] : Pack E) ≠ ([E.range] ++ [E.parse] : Pack E)
example : ([E.parse, E.parse] : Pack E) ≠ [E.parse] := by decide

end Tests
