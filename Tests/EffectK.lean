import Graded.EffectK

/-! Examples instantiating `Graded.Effect`'s classes and laws at both
    carriers, at the concrete error type `E`.

    The point of these is not that the laws hold — they hold because each
    instance field cites a theorem already proved and tested in its own
    module. The point is that the *instances resolve*, that the abstract
    `Effect.pureK` agrees with each carrier's own, and that the generic law
    statements apply at a concrete grade without any bridging. -/

namespace Tests.EffectK

open Graded Graded.Effect

/-- This file's own error type. `Graded.Obligations` declares a
    `Graded.E` as its counter-instance fixture and `Graded.EffectK`
    imports it, so `open Graded` together with `Examples.Validation`
    makes every `EK.parse` ambiguous — and `hiding E` does not help,
    because it is the constructor path that collides. A local type is
    what `Tests/Canonical.lean` already does when the shared fixture
    does not fit. -/
inductive EK | parse | range | io
  deriving DecidableEq, Repr

abbrev GP : Grade EK := {EK.parse}
abbrev GR : Grade EK := {EK.range}
abbrev KK : Grade EK := {EK.parse, EK.range, EK.io}

theorem hp : GP ⊆ KK := by decide
theorem hr : GR ⊆ KK := by decide

-- ---------------------------------------------------------------------
-- Every class resolves at `Graded`, and every law class with it.

example : GradedFunctorK (Grade EK) (Graded.Graded (Err := EK)) := inferInstance
example : GradedMonadK (Grade EK) (Graded.Graded (Err := EK)) := inferInstance
example : GradedApplicativeK (Grade EK) (Graded.Graded (Err := EK)) := inferInstance
example : LawfulGradedFunctorK (Grade EK) (Graded.Graded (Err := EK)) := inferInstance
example : LawfulGradedMonadK (Grade EK) (Graded.Graded (Err := EK)) := inferInstance
example : LawfulGradedApplicativeK (Grade EK) (Graded.Graded (Err := EK)) := inferInstance

-- ---------------------------------------------------------------------
-- `Accum` is a graded applicative and **not** a graded monad. There is no
-- `example : GradedMonadK (Grade EK) Accum := inferInstance` in this file,
-- because it must not typecheck: `Accum.notMonad` is the reason, and it
-- is instantiated in `Tests/Accum.lean`.

example : GradedFunctorK (Grade EK) (Graded.Accum (Err := EK)) := inferInstance
example : GradedApplicativeK (Grade EK) (Graded.Accum (Err := EK)) := inferInstance
example : LawfulGradedFunctorK (Grade EK) (Graded.Accum (Err := EK)) := inferInstance
example : LawfulGradedApplicativeK (Grade EK) (Graded.Accum (Err := EK)) := inferInstance

-- ---------------------------------------------------------------------
-- The derived `Effect.pureK` is each carrier's own `pure`, at any grade. Both
-- are `rfl`, which is the reason `Effect.pureK` could be derived rather than
-- made a primitive field with a coherence law attached.

example (a : Nat) : (Effect.pureK a : Graded.Graded KK Nat) = Graded.pureK a := rfl
example (a : Nat) : (Effect.pureK a : Graded.Accum KK Nat) = Graded.Accum.pureK a := rfl

/-- Render a `Graded` result at the nominated grade, for `#guard`. -/
def renderKK : Graded.Graded KK Nat → String
  | .ok n => s!"ok {n}"
  | .err e _ => s!"err {repr e}"

#guard renderKK (Effect.pureK (42 : Nat) : Graded.Graded KK Nat) = "ok 42"

-- ---------------------------------------------------------------------
-- The generic laws, applied at concrete grades. Each is stated through
-- the class projection, so what is being exercised is the abstract
-- statement resolving against the concrete instance — not the concrete
-- theorem under a different name.

example (x : Graded.Graded GP Nat) : GradedFunctorK.map id x = x :=
  LawfulGradedFunctorK.map_id x

example (h₁ : GP ⊆ GR ∪ GP) (f : Nat → Nat) (x : Graded.Graded GP Nat) :
    GradedFunctorK.widen h₁ (GradedFunctorK.map f x)
      = GradedFunctorK.map f (GradedFunctorK.widen h₁ x) :=
  LawfulGradedFunctorK.widen_map h₁ f x

example (a : Nat) (f : Nat → Graded.Graded GR Nat) :
    GradedMonadK.bindK (PreorderedGradeMonoid.bot_le KK) hr (GradedFunctorK.pure a) f
      = GradedFunctorK.widen hr (f a) :=
  LawfulGradedMonadK.bindK_pure_left hr a f

example (x : Graded.Graded GP Nat) :
    GradedMonadK.bindK hp (PreorderedGradeMonoid.bot_le KK) x GradedFunctorK.pure
      = GradedFunctorK.widen hp x :=
  LawfulGradedMonadK.bindK_pure_right hp x

-- The applicative laws at *both* carriers, which is the discriminating
-- case: the two agree on every law below and disagree on whether a monad
-- exists at all.

example (x : Graded.Graded GR Nat) :
    GradedApplicativeK.apK (PreorderedGradeMonoid.le_refl' KK) hr (Effect.pureK (@id Nat)) x
      = GradedFunctorK.widen hr x :=
  LawfulGradedApplicativeK.apK_pure_id hr x

example (x : Graded.Accum GR Nat) :
    GradedApplicativeK.apK (PreorderedGradeMonoid.le_refl' KK) hr
        (Effect.pureK (@id Nat) : Graded.Accum KK (Nat → Nat)) x
      = GradedFunctorK.widen hr x :=
  LawfulGradedApplicativeK.apK_pure_id hr x

example (u : Graded.Accum GP (Nat → Nat)) (a : Nat) :
    GradedApplicativeK.apK hp (PreorderedGradeMonoid.le_refl' KK) u
        (Effect.pureK a : Graded.Accum KK Nat)
      = GradedApplicativeK.apK (PreorderedGradeMonoid.le_refl' KK) hp
          (Effect.pureK (fun f => f a) : Graded.Accum KK ((Nat → Nat) → Nat)) u :=
  LawfulGradedApplicativeK.apK_interchange hp u a

-- `apK_comp` at `Accum` is the one law that is not `rfl` for this
-- carrier: three failing sides accumulate, and the two groupings differ
-- by `List.append_assoc`. Instantiated at three *distinct* grades and
-- three failing values, so the associativity is actually exercised.
example (u : Graded.Accum GP (Nat → Nat)) (v : Graded.Accum GR (Nat → Nat))
    (w : Graded.Accum ({EK.io} : Grade EK) Nat) (hj : ({EK.io} : Grade EK) ⊆ KK) :
    GradedApplicativeK.apK (PreorderedGradeMonoid.le_refl' KK) hj
        (GradedApplicativeK.apK (PreorderedGradeMonoid.le_refl' KK) hr
          (GradedApplicativeK.apK (PreorderedGradeMonoid.le_refl' KK) hp
            (Effect.pureK Function.comp
              : Graded.Accum KK ((Nat → Nat) → (Nat → Nat) → Nat → Nat)) u) v) w
      = GradedApplicativeK.apK hp (PreorderedGradeMonoid.le_refl' KK) u
          (GradedApplicativeK.apK hr hj v w) :=
  LawfulGradedApplicativeK.apK_comp hp hr hj u v w

-- ---------------------------------------------------------------------
-- The polymorphic traversal, at both carriers, and the two statements
-- that it *is* each carrier's own traversal.

/-- Fails on `0`, succeeds otherwise: the same fixture shape used for the
    concrete traversals, so the generic one is exercised on a list that
    both succeeds and fails. -/
def checkG (n : Nat) : Graded.Graded GP Nat :=
  if n = 0 then Graded.Graded.err EK.parse (by decide) else Graded.Graded.ok (n + 1)

def checkA (n : Nat) : Graded.Accum GP Nat :=
  if n = 0 then Graded.Accum.errs [EK.parse] (by simp) (by intro e he; simp at he; simp [he])
  else Graded.Accum.ok (n + 1)

example (xs : List Nat) : traverseGK hp checkG xs = Graded.traverseK hp checkG xs :=
  traverseGK_eq_traverseK hp checkG xs

example (xs : List Nat) : traverseGK hp checkA xs = Graded.Accum.traverseK hp checkA xs :=
  traverseGK_eq_accum_traverseK hp checkA xs

example (h : Nat → Nat) (xs : List Nat) :
    traverseGK hp checkG (xs.map h) = traverseGK hp (checkG ∘ h) xs :=
  traverseGK_map hp checkG h xs

example (xs : List Nat) :
    traverseGK (PreorderedGradeMonoid.le_refl' KK)
        (fun a => (Effect.pureK a : Graded.Graded KK Nat)) xs = Effect.pureK xs :=
  traverseGK_pureK xs

example (xs : List Nat) :
    traverseGK (PreorderedGradeMonoid.le_refl' KK)
        (fun a => (Effect.pureK a : Graded.Accum KK Nat)) xs = Effect.pureK xs :=
  traverseGK_pureK xs

example (f : Nat → Nat) (a : Nat) :
    GradedFunctorK.map f (Effect.pureK a : Graded.Graded KK Nat) = Effect.pureK (f a) :=
  map_pureK f a

-- The generic traversal computes at both carriers, on a list with a
-- failure in it and one without.

def renderGL : Graded.Graded KK (List Nat) → String
  | .ok ns => s!"ok {ns}"
  | .err e _ => s!"err {repr e}"

def renderAL : Graded.Accum KK (List Nat) → String
  | .ok ns => s!"ok {ns}"
  | .errs es _ _ => s!"errs {es.length}"

#guard renderGL (traverseGK hp checkG [1, 2, 3]) = "ok [2, 3, 4]"
#guard renderGL (traverseGK hp checkG [1, 0, 0]) = "err Tests.EffectK.EK.parse"
#guard renderAL (traverseGK hp checkA [1, 2, 3]) = "ok [2, 3, 4]"
-- Two failures accumulate at the accumulating carrier and short-circuit
-- at the other, from the *same* generic definition.
#guard renderAL (traverseGK hp checkA [1, 0, 0]) = "errs 2"

-- ---------------------------------------------------------------------
-- The third carrier. `Comp` is graded by a *pair*, and fits the same
-- one-grade interface only because a pair of grades is now itself a
-- grade. Data instances only — see `Graded/EffectK.lean` for which laws
-- `Comp` does not yet have at the sufficient grade.

example : PreorderedGradeMonoid (Grade EK × Grade EK) := inferInstance
example : IsLubGrade (Grade EK × Grade EK) := inferInstance
example : GradedFunctorK (Grade EK × Grade EK) (CompP EK) := inferInstance
example : GradedApplicativeK (Grade EK × Grade EK) (CompP EK) := inferInstance

/-- A check into the composite carrier: outer grade `{parse}`, inner
    grade `{range}`, so the two coordinates are *different* grades and the
    product is not a diagonal in disguise. -/
def checkC (n : Nat) : CompP EK (GP, GR) Nat :=
  Graded.Graded.ok (Graded.Graded.ok (n + 1))

-- The product inclusion is the two componentwise inclusions already
-- proved above, paired. `PreorderedGradeMonoid.le` on the product is
-- definitionally that conjunction, so this needs no new proof.
theorem hpr : PreorderedGradeMonoid.le ((GP, GR) : Grade EK × Grade EK) (KK, KK) :=
  ⟨hp, hr⟩

-- The *same* generic traversal, at the composite carrier.
def renderCL : CompP EK (KK, KK) (List Nat) → String
  | .ok (.ok ns) => s!"ok ok {ns}"
  | .ok (.err e _) => s!"ok err {repr e}"
  | .err e _ => s!"err {repr e}"

#guard renderCL (traverseGK hpr checkC [1, 2, 3]) = "ok ok [2, 3, 4]"

-- ---------------------------------------------------------------------
-- The transformation, and naturality proved once.

example (a : Nat) : toGradedTransformation.app (Effect.pureK a : Graded.Accum KK Nat)
    = Effect.pureK a :=
  ApplicativeTransformationK.app_pureK toGradedTransformation a

example (xs : List Nat) :
    toGradedTransformation.app (traverseGK hp checkA xs)
      = traverseGK hp (fun a => toGradedTransformation.app (checkA a)) xs :=
  ApplicativeTransformationK.app_traverseGK toGradedTransformation hp checkA xs

/-- [accum-traverse]'s theorem, recovered from the generic law. -/
example (xs : List Nat) :
    Graded.Accum.toGraded (Graded.Accum.traverseK hp checkA xs)
      = Graded.traverseK hp (fun a => Graded.Accum.toGraded (checkA a)) xs :=
  toGraded_traverseK_generic hp checkA xs

-- And it agrees with the concrete theorem it replaces, on a list where
-- two positions fail: the accumulating traversal collects both, the
-- projection keeps the first.
#guard renderGL (Graded.Accum.toGraded (Graded.Accum.traverseK hp checkA [1, 0, 0]))
  = "err Tests.EffectK.EK.parse"

end Tests.EffectK
