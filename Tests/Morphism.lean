import Graded.Morphism
import Examples.Validation

/-! Examples instantiating every `Graded.Morphism` theorem at the concrete
    coarsening `coarsen : E → E'` from `Examples.Validation`, plus a
    `#guard` on `Grade.rename` and one on `rename` (through `renderCoarse`,
    per the `#guard`-on-`Graded` detour every consumer in this codebase
    has needed since [monad-laws]) that both compute. -/

namespace Tests

open Graded Graded.Accum Examples.Validation

-- ---------------------------------------------------------------------
-- `Grade.rename`: the homomorphism, and the order-preservation, at the
-- concrete `coarsen`.

example : Grade.rename coarsen (Grade.join ({E.parse} : Grade E) {E.range}) =
    Grade.join (Grade.rename coarsen {E.parse}) (Grade.rename coarsen {E.range}) :=
  Grade.rename_join coarsen {E.parse} {E.range}

example : Grade.rename coarsen (Grade.bot : Grade E) = Grade.bot :=
  Grade.rename_bot coarsen

example : Grade.rename coarsen ({E.parse} : Grade E) ⊆ Grade.rename coarsen {E.parse, E.range} :=
  Grade.rename_mono coarsen (by decide)

-- `Grade.rename` computes.
#guard Grade.rename coarsen ({E.parse, E.range} : Grade E) = ({E'.bad} : Grade E')

-- ---------------------------------------------------------------------
-- `rename`: naturality in the payload, and commuting with `widen`/`cast`.

example : rename coarsen (map (· + 1) (parseNat "41")) =
    map (· + 1) (rename coarsen (parseNat "41")) :=
  rename_map coarsen (· + 1) (parseNat "41")

example (h₁ : ({E.parse} : Grade E) ⊆ {E.parse, E.range}) :
    rename coarsen (widen h₁ (parseNat "abc")) =
      widen (Grade.rename_mono coarsen h₁) (rename coarsen (parseNat "abc")) :=
  rename_widen coarsen h₁ (parseNat "abc")

example (e : ({E.parse} : Grade E) = {E.parse}) :
    rename coarsen (cast e (parseNat "abc")) =
      cast (congrArg (Grade.rename coarsen) e) (rename coarsen (parseNat "abc")) :=
  rename_cast coarsen e (parseNat "abc")

example (n : Nat) :
    cast (Grade.rename_bot coarsen)
        (rename coarsen (Graded.pure n : Graded (Grade.bot : Grade E) Nat)) =
      Graded.pure n :=
  rename_pure coarsen n

-- ---------------------------------------------------------------------
-- `rename` is a monad/applicative morphism: commutes with `bind`, `ap`,
-- `map2`, up to `Grade.rename_join`.

example :
    cast (Grade.rename_join coarsen ({E.parse} : Grade E) {E.range})
        (rename coarsen (bind (parseNat "42") checkRange)) =
      bind (rename coarsen (parseNat "42")) (rename coarsen ∘ checkRange) :=
  rename_bind coarsen (parseNat "42") checkRange

example :
    cast (Grade.rename_join coarsen ({E.parse} : Grade E) {E.range})
        (rename coarsen (ap (map (· + ·) (parseNat "3")) (checkRange 4))) =
      ap (rename coarsen (map (· + ·) (parseNat "3"))) (rename coarsen (checkRange 4)) :=
  rename_ap coarsen (map (· + ·) (parseNat "3")) (checkRange 4)

example :
    cast (Grade.rename_join coarsen ({E.parse} : Grade E) {E.range})
        (rename coarsen (map2 (· + ·) (parseNat "3") (checkRange 4))) =
      map2 (· + ·) (rename coarsen (parseNat "3")) (rename coarsen (checkRange 4)) :=
  rename_map2 coarsen (· + ·) (parseNat "3") (checkRange 4)

-- ---------------------------------------------------------------------
-- `GradedHom`/`renameHom`: the general definition, instantiated at
-- `coarsen`, exposes exactly the fields `rename_join`/`rename_bot`/
-- `rename_bind`/`rename_pure` already proved.

example : (renameHom coarsen : GradedHom E E').gmap = Grade.rename coarsen := rfl

-- ---------------------------------------------------------------------
-- Naturality of `traverse` against `rename`.

example (ss : List String) :
    rename coarsen (traverse parseNat ss) = traverse (rename coarsen ∘ parseNat) ss :=
  traverse_rename coarsen parseNat ss

-- ---------------------------------------------------------------------
-- `Accum.rename`/`rename_toGraded`, at the concrete `parseNatAccum`.

example (x : Accum ({E.parse} : Grade E) Nat) :
    Graded.rename coarsen (toGraded x) = toGraded (Accum.rename coarsen x) :=
  Accum.rename_toGraded coarsen x

-- `rename` on the carrier computes, through `renderCoarse` (direct
-- `Graded`/`Accum` equality has never worked in this codebase's `#guard`s
-- since [monad-laws]).
#guard renderCoarse (rename coarsen (validate "42")) = "ok 42"
#guard renderCoarse (rename coarsen (validate "abc")) = "err Examples.Validation.E'.bad"

end Tests
