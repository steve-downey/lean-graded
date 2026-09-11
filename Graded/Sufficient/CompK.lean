import Graded.Sufficient.ComposeK
import Graded.Sufficient.TraversableK
import Graded.ComposeApp

/-! `Comp.apK`/`traverseCompK`: the product-graded composite.

    Split out of the former single `Graded/Sufficient.lean` by
    [module-split]; `Graded.Sufficient` is now a re-export shim over the
    six pieces, so every existing import keeps working. -/

namespace Graded

variable {Err : Type u} [DecidableEq Err]
variable {g h j k : Grade Err} {α β γ : Type v}

-- ---------------------------------------------------------------------
-- `Comp.apK`: the composed applicative at a *pair* of sufficient grades.
-- `Comp g h α` ([compose]) already generalises over any two grades, so no
-- second carrier is needed — "sufficient" here means supplying `Comp`'s
-- own two indices as caller-chosen bounds `k1`/`k2` instead of the
-- componentwise joins `Comp.ap` computes. Built through `map2K`/`apK`
-- exactly as `Comp.ap` is built through `Graded.map2`/`Graded.ap`: outer
-- combine at `k1`, with the *inner* `apK` (at `k2`) threaded through as
-- the combining function.

section CompK

variable {g' h' j' k1 k2 : Grade Err} {α β γ δ : Type u}

/-- The composed applicative at a sufficient grade *pair* `(k1, k2)`. -/
def Comp.apK (hg : g ⊆ k1) (hg' : g' ⊆ k1) (hh : h ⊆ k2) (hh' : h' ⊆ k2)
    (ff : Comp g h (α → β)) (xx : Comp g' h' α) : Comp k1 k2 β :=
  Graded.map2K hg hg'
    (fun (F : Graded h (α → β)) (X : Graded h' α) => Graded.apK hh hh' F X) ff xx

-- Reduction lemmas: the two-coordinate mirror of `apK_ok_ok`/
-- `apK_err_left`/`apK_ok_err`, all `rfl` for the same reason.

theorem Comp.apK_ok_ok (hg : g ⊆ k1) (hg' : g' ⊆ k1) (hh : h ⊆ k2) (hh' : h' ⊆ k2)
    (F : Graded h (α → β)) (X : Graded h' α) :
    Comp.apK hg hg' hh hh' (Graded.ok F : Comp g h (α → β)) (Graded.ok X : Comp g' h' α) =
      Graded.ok (Graded.apK hh hh' F X) := rfl

theorem Comp.apK_err_left (hg : g ⊆ k1) (hg' : g' ⊆ k1) (hh : h ⊆ k2) (hh' : h' ⊆ k2)
    (e : Err) (he : e ∈ g) (xx : Comp g' h' α) :
    Comp.apK hg hg' hh hh' (Graded.err e he : Comp g h (α → β)) xx =
      Graded.err e (hg he) := rfl

theorem Comp.apK_ok_err (hg : g ⊆ k1) (hg' : g' ⊆ k1) (hh : h ⊆ k2) (hh' : h' ⊆ k2)
    (F : Graded h (α → β)) (e : Err) (he : e ∈ g') :
    Comp.apK hg hg' hh hh' (Graded.ok F : Comp g h (α → β)) (Graded.err e he : Comp g' h' α) =
      Graded.err e (hg' he) := rfl

-- ---------------------------------------------------------------------
-- The headline measurement. `Comp.ap_interchange`, stated at the computed
-- componentwise-join grade, needs `Comp.castGH` on both sides — two
-- `Graded.cast`s per side, driven by `Grade.join_bot`/`Grade.bot_join` in
-- each of the two components separately. At a common sufficient grade
-- pair, both sides of `Comp.apK`'s interchange law already land in
-- `Comp k1 k2 β`: **zero** casts, and (unlike `Comp.ap_interchange`,
-- which cites `Graded.ap_interchange` — unit, twice — in its `ok`
-- branch) the fully case-split proof below closes by `rfl` alone: there
-- is no property left to cite.

theorem Comp.apK_interchange (hg : g ⊆ k1) (hh : h ⊆ k2) (u : Comp g h (α → β)) (a : α) :
    Comp.apK hg (Grade.bot_le k1) hh (Grade.bot_le k2) u (Comp.pure a) =
      Comp.apK (Grade.bot_le k1) hg (Grade.bot_le k2) hh
        (Comp.pure (fun f => f a) : Comp Grade.bot Grade.bot ((α → β) → β)) u := by
  cases u using Graded.rec' with
  | err e he => rfl
  | ok F =>
    cases F using Graded.rec' with
    | ok f' => rfl
    | err e he => rfl

-- ---------------------------------------------------------------------
-- `traverseCompK`: the composed traversal at a sufficient grade *pair*,
-- built the same way `traverseK` was one layer down — through
-- `Comp.map2K`/`Comp.pureK`, both landing directly at `(k1, k2)`, with no
-- `Comp.traverseRaw`/`foldGrade` anywhere. Where `traverseComp` folds each
-- component's grade once per list element and then widens the uniform
-- result via `Comp.widenGH` along `Graded.foldGrade_le` (once per
-- component), `traverseCompK` never folds at all: every element's image
-- under `f` (at the fixed pair `(g, h)`) and the accumulated tail
-- (already at `(k1, k2)`) combine directly, reusing `hg`/`hh` at every
-- position exactly as `traverseK` reuses its own single `hg`.

/-- `Comp`'s own `pureK`: both layers at any grade pair `(k1, k2)`
    directly, nesting `Graded.pureK` inside itself — `Graded.pureK a :
    Graded k2 α` is already `.ok a` regardless of `k2`
    (`Graded.fromEmpty_eq_ok`), so wrapping it again at `k1` gives
    `.ok (.ok a)` before any grade is inspected, the `Comp.pure` this leg
    needs at a caller-chosen pair instead of `(⊥, ⊥)`. -/
def Comp.pureK (a : α) : Comp k1 k2 α := Graded.pureK (Graded.pureK a)

/-- `Comp`'s own `map2K`: `Comp.apK` after `Comp.map`, exactly as
    `Comp.map2` is `Comp.ap` after `Comp.map`, and exactly as `map2K` is
    `apK` after `map` one layer down. -/
def Comp.map2K (hg : g ⊆ k1) (hg' : g' ⊆ k1) (hh : h ⊆ k2) (hh' : h' ⊆ k2)
    (kfun : α → β → γ) (x : Comp g h α) (y : Comp g' h' β) : Comp k1 k2 γ :=
  Comp.apK hg hg' hh hh' (Comp.map kfun x) y

/-- The composed traversal at a sufficient grade pair `(k1, k2)`: a
    uniform `f : α → Comp g h β` lifts to `List α → Comp k1 k2 (List β)`,
    at the same grade pair regardless of the list's length — no fold,
    the same shape `traverseK` already established one layer down. -/
def traverseCompK (hg : g ⊆ k1) (hh : h ⊆ k2) (f : α → Comp g h β) :
    List α → Comp k1 k2 (List β)
  | []      => Comp.pureK []
  | x :: xs => Comp.map2K hg (Grade.le_refl' k1) hh (Grade.le_refl' k2)
      (· :: ·) (f x) (traverseCompK hg hh f xs)

theorem traverseCompK_nil (hg : g ⊆ k1) (hh : h ⊆ k2) (f : α → Comp g h β) :
    traverseCompK hg hh f ([] : List α) = Comp.pureK [] := rfl

theorem traverseCompK_cons (hg : g ⊆ k1) (hh : h ⊆ k2) (f : α → Comp g h β) (x : α)
    (xs : List α) :
    traverseCompK hg hh f (x :: xs) =
      Comp.map2K hg (Grade.le_refl' k1) hh (Grade.le_refl' k2)
        (· :: ·) (f x) (traverseCompK hg hh f xs) := rfl

/-- Which proof of `g ⊆ k1`/`h ⊆ k2` justifies `traverseCompK` doesn't
    matter, only that one exists — the two-coordinate mirror of
    `traverseK_irrel`. -/
theorem traverseCompK_irrel (hg hg' : g ⊆ k1) (hh hh' : h ⊆ k2) (f : α → Comp g h β)
    (xs : List α) :
    traverseCompK hg hh f xs = traverseCompK hg' hh' f xs := rfl

-- ---------------------------------------------------------------------
-- `traverseCompK_eq`: the law [sufficient-grade-nested] exists to check.
-- `traverseComp_eq` ([compose](../docs/design.md#compose)) holds
-- *unconditionally* at the union-graded layer — no `flatten`, no
-- hypothesis, consuming only `Grade.join_idem` (via `traverse_cons`, once
-- per component) and no `Grade.join_comm` at all. At a sufficient grade
-- pair there is no fold and hence no idempotence to pay in the first
-- place (`traverseCompK_cons`, like `traverseK_cons`, is `rfl`): this
-- theorem is the confirmation the step file asked for, not a new finding
-- — the classical composition law, stated against the unflattened pair,
-- survives cast-free at a sufficient grade exactly as it held
-- unconditionally at the computed one. Had this analogue *failed*, that
-- would have been a serious finding about the sufficient-grade design,
-- since `traverseComp_eq` is the theorem that settled
-- [graded-traversable-composition](../docs/design.md#graded-traversable-composition);
-- it does not fail.
theorem traverseCompK_eq (hg : g ⊆ k1) (hh : h ⊆ k2)
    (f : α → Graded g β) (kf : β → Graded h γ) (xs : List α) :
    traverseCompK hg hh (fun a => Graded.map kf (f a)) xs =
      Graded.map (traverseK hh kf) (traverseK hg f xs) := by
  induction xs with
  | nil => rfl
  | cons x xs' ih =>
      rw [traverseCompK_cons, ih, traverseK_cons]
      cases hfx : f x using Graded.rec' with
      | err e he =>
          simp only [Graded.map, Comp.map2K, Comp.apK, Comp.map, Graded.map2K, apK_err_left]
      | ok a =>
          cases hxs : traverseK hg f xs' using Graded.rec' with
          | err e he =>
              simp only [Graded.map, Comp.map2K, Comp.apK, Comp.map, Graded.map2K, apK_ok_err]
          | ok l =>
              simp only [Graded.map, Comp.map2K, Comp.apK, Comp.map, Graded.map2K, apK_ok_ok]
              exact congrArg Graded.ok (traverseK_cons hh kf a l).symm

-- ---------------------------------------------------------------------
-- `Comp.grade_reassoc`'s analogue: unnecessary, and none is missing.
-- `Comp.grade_reassoc` ([compose](../docs/design.md#compose)) exists
-- purely to make `flatten_ap`'s cast typecheck — reassociating `(g ⊔ h) ⊔
-- (g' ⊔ h')` into `(g ⊔ g') ⊔ (h ⊔ h')`, a pure grade-level equation with
-- no carrier in sight, needing both `Grade.join_assoc` and
-- `Grade.join_comm`. `flatten_apK` below never introduces a `cast` at
-- all: `flattenK`'s target and `apK`'s target are both the caller's own
-- `k`, so there is no equation between two different expressions for the
-- same grade anywhere in its statement for a reassociation lemma to be
-- stated about. This is the same "no analogue, and none is missing"
-- verdict [sufficient-grade-morphism] reached for `rename_cast`, one leg
-- earlier — a fact that exists only to serve a `cast` disappears along
-- with the `cast` it served.

/-- `flatten` is an applicative morphism from the product-graded composite
    to the union-graded carrier only under a one-sided condition
    ([compose](../docs/design.md#compose)); `flattenK`/`Comp.apK` is the
    same comparison at a common sufficient grade `k`, and the condition
    survives unchanged — it is about which error a caller sees when
    `ff`'s outer layer succeeds with a failing inner payload while `xx`'s
    outer layer also fails, and no amount of grade nomination touches
    that. What does dissolve is the grade side: both sides below already
    land in `Graded k β`, so there is no `cast`, no `Comp.grade_reassoc`
    analogue, and — since `flattenK`/`apK`/`Comp.apK` never compute a
    `join` — no `Grade.join_comm` anywhere in the proof. -/
theorem flatten_apK (hg : g ⊆ k1) (hg' : g' ⊆ k1) (hh : h ⊆ k2) (hh' : h' ⊆ k2)
    (hk1 : k1 ⊆ k) (hk2 : k2 ⊆ k)
    (ff : Comp g h (α → β)) (xx : Comp g' h' α)
    (hcond : (∃ e he, ff = Graded.err e he) ∨ (∃ f', ff = Graded.ok (Graded.ok f')) ∨
      (∃ X, xx = Graded.ok X)) :
    flattenK hk1 hk2 (Comp.apK hg hg' hh hh' ff xx) =
      apK (Grade.le_refl' k) (Grade.le_refl' k)
        (flattenK (Grade.le_trans' hg hk1) (Grade.le_trans' hh hk2) ff)
        (flattenK (Grade.le_trans' hg' hk1) (Grade.le_trans' hh' hk2) xx) := by
  cases ff using Graded.rec' with
  | err e he =>
    cases xx using Graded.rec' with
    | ok Y =>
      cases Y using Graded.rec' with
      | ok a =>
        simp only [Comp.apK_err_left, flattenK_err, flattenK_ok, widen_ok, apK_err_left]
      | err e' he' =>
        simp only [Comp.apK_err_left, flattenK_err, flattenK_err, apK_err_left]
    | err e' he' =>
      simp only [Comp.apK_err_left, flattenK_err, flattenK_err, apK_err_left]
  | ok F =>
    cases xx using Graded.rec' with
    | err e he =>
      cases F using Graded.rec' with
      | ok f' =>
        simp only [Comp.apK_ok_err, flattenK_ok, flattenK_err, widen_ok, apK_ok_err]
      | err e' he' =>
        exfalso
        rcases hcond with ⟨_, _, hff⟩ | ⟨_, hff⟩ | ⟨_, hxx⟩ <;> simp_all
    | ok X =>
      cases F using Graded.rec' with
      | ok f' =>
        cases X using Graded.rec' with
        | ok a =>
          simp only [Comp.apK_ok_ok, flattenK_ok, apK_ok_ok, widen_ok]
        | err e he =>
          simp only [Comp.apK_ok_ok, flattenK_ok, apK_ok_err, widen_ok, widen_err]
      | err e he =>
        cases X using Graded.rec' with
        | ok a =>
          simp only [Comp.apK_ok_ok, flattenK_ok, apK_err_left, widen_ok, widen_err]
        | err e' he' =>
          simp only [Comp.apK_ok_ok, flattenK_ok, apK_err_left, widen_err]

end CompK

end Graded
