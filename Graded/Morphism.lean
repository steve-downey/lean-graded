import Graded.Traverse
import Graded.Accum
import Mathlib.Data.Finset.Image

/-! Grade morphisms: what it means to rename or coarsen error kinds. In
    C++, `error_set<A, B>` maps to `error_set<C>` by sending both `A` and
    `B` to `C` — a `transform_error`-style operation, not a general
    functor on the payload. This module gives it a Lean type: a function
    `φ : Err → Err'` on error *kinds*, lifted to grades by `Finset.image`
    and to carriers by `rename`, and proves it is a graded monad morphism
    — the naturality law `traverse` needs to talk about applicative
    morphisms at all.

    The finding this module records: `Finset.image` preserves `join`
    (union) and `bot` (∅) *unconditionally*, for *any* `φ`, with no
    injectivity or surjectivity hypothesis anywhere — it is a
    homomorphism of join-semilattices, full stop. It does **not**
    preserve meet, complement, or anything to do with the *order* being a
    genuine lattice rather than a join-semilattice, but this design never
    needed those. `rename_mono` (inclusion is preserved) follows for
    free from the same fact, since `⊆` on a `Finset` is definable from
    `∪` (`Grade.join_eq_right_of_le`), though it is proved directly here
    from `Finset.image_subset_image` rather than routed through that
    definition. -/

namespace Graded

namespace Grade
variable {Err : Type u} [DecidableEq Err] {Err' : Type u} [DecidableEq Err']

/-- Rename every error kind along `φ`. Models the C++ `error_set<A, B> →
    error_set<C>` map that collapses two source kinds to one target kind
    when `φ` sends both `A` and `B` to `C` — `φ` need not be injective. -/
def rename (φ : Err → Err') : Grade Err → Grade Err' := Finset.image φ

/-- PROPERTY: homomorphism -/
theorem rename_join (φ : Err → Err') (g h : Grade Err) :
    rename φ (Grade.join g h) = Grade.join (rename φ g) (rename φ h) :=
  Finset.image_union (f := φ) g h

/-- PROPERTY: homomorphism -/
theorem rename_bot (φ : Err → Err') : rename φ (Grade.bot : Grade Err) = Grade.bot :=
  Finset.image_empty φ

/-- (order) Renaming preserves inclusion: `φ` is a monotone map from
    `(Grade Err, ⊆)` to `(Grade Err', ⊆)`. Needs no hypothesis on `φ`
    beyond being a plain function — the same "no injectivity, no
    surjectivity" finding as `rename_join`/`rename_bot`. -/
theorem rename_mono {g h : Grade Err} (φ : Err → Err') (hgh : g ⊆ h) :
    rename φ g ⊆ rename φ h :=
  Finset.image_subset_image hgh

/-- `Finset.mem_image_of_mem`, restated with its conclusion pinned to
    `Grade.rename` by name rather than left as the `Finset.image` it
    unfolds to. Needed because `Graded.err`'s grade index is inferred
    from its membership-proof argument's *stated* type, not from any
    later defeq-unfolding: without this restatement, every downstream
    `Graded.err (φ e) (Finset.mem_image_of_mem φ he)` term ends up
    indexed by the unfolded `Finset.image φ g` rather than the folded
    `Grade.rename φ g`, and `rw`/`simp` (syntactic up to reducible
    transparency) then fail to match it against lemmas stated in terms
    of `Grade.rename`, even though the two are definitionally equal. -/
theorem mem_rename {φ : Err → Err'} {e : Err} {g : Grade Err} (he : e ∈ g) :
    φ e ∈ rename φ g :=
  Finset.mem_image_of_mem φ he

end Grade

variable {Err : Type u} [DecidableEq Err] {Err' : Type u} [DecidableEq Err']
variable {g g' h j : Grade Err} {α β γ : Type v}

/-- Rename every error kind a graded value might carry, along `φ`: `ok`
    is untouched, `err` carries its error through `φ` and its membership
    proof through `Grade.mem_rename`. Models the C++
    `transform_error`-style conversion `expected<T, error_set<Es...>> →
    expected<T, error_set<Es'...>>` given `Es... → Es'...`. -/
def rename (φ : Err → Err') : Graded g α → Graded (Grade.rename φ g) α
  | .ok a     => .ok a
  | .err e he => .err (φ e) (Grade.mem_rename he)

theorem rename_ok (φ : Err → Err') (a : α) :
    (rename φ (Graded.ok a : Graded g α)) = Graded.ok a := rfl

theorem rename_err (φ : Err → Err') (e : Err) (he : e ∈ g) :
    (rename φ (Graded.err e he : Graded g α)) =
      Graded.err (φ e) (Grade.mem_rename he) := rfl

/-- `rename` is natural in the payload: mapping before or after renaming
    agrees, and needs no cast — renaming leaves the grade `Grade.rename φ
    g` fixed on both sides, so this is a strict equality, not merely one
    up to a pomonoid law. -/
theorem rename_map (φ : Err → Err') (f : α → β) (x : Graded g α) :
    rename φ (map f x) = map f (rename φ x) := by
  cases x with
  | ok a => rfl
  | err e he => rfl

/-- `rename` commutes with `widen`, along the monotone image of the
    inclusion (`Grade.rename_mono`). -/
theorem rename_widen (φ : Err → Err') (h₁ : g ⊆ g') (x : Graded g α) :
    rename φ (widen h₁ x) = widen (Grade.rename_mono φ h₁) (rename φ x) := by
  cases x with
  | ok a => rfl
  | err e he => rfl

/-- `rename` commutes with `cast`, transported along the image of the
    grade equality. -/
theorem rename_cast (φ : Err → Err') (e : g = g') (x : Graded g α) :
    rename φ (cast e x) = cast (congrArg (Grade.rename φ) e) (rename φ x) := by
  subst e; rfl

/-- `rename` of `pure` is `pure`, up to `Grade.rename_bot` — `pure` never
    carries an error, so renaming has nothing to do, but the *type* still
    needs the grade transported since `Grade.rename φ Grade.bot` is not
    syntactically `Grade.bot`. -/
theorem rename_pure (φ : Err → Err') (a : α) :
    cast (Grade.rename_bot φ) (rename φ (pure a : Graded (Grade.bot : Grade Err) α)) =
      pure a := by
  simp only [pure, rename_ok]
  exact cast_ok (Grade.rename_bot φ) a

/-- `rename` is a monad morphism: it commutes with `bind`, up to
    `Grade.rename_join` transporting the joined grade. The cast sits on
    the "renamed compound" side — `rename φ (bind x f)`, whose grade is
    `Grade.rename φ (Grade.join g h)` — matching the convention every
    `bind`/`ap` law in this codebase already uses (cast on the side whose
    grade is the *un-distributed* expression). -/
theorem rename_bind (φ : Err → Err') (x : Graded g α) (f : α → Graded h β) :
    cast (Grade.rename_join φ g h) (rename φ (bind x f)) =
      bind (rename φ x) (rename φ ∘ f) := by
  cases x with
  | ok a =>
    simp only [bind, Function.comp_apply, rename_ok]
    rw [rename_widen, cast_widen]
  | err e he =>
    simp only [bind, rename_err]
    rw [cast_err]

/-- `rename` commutes with `ap`, up to `Grade.rename_join`. Proved
    directly from `ap`'s reduction lemmas rather than through `bind`,
    matching how `ap_ok_ok`/`ap_err_left`/`ap_ok_err` are themselves
    proved once and reused. -/
theorem rename_ap (φ : Err → Err') (f : Graded g (α → β)) (x : Graded h α) :
    cast (Grade.rename_join φ g h) (rename φ (ap f x)) =
      ap (rename φ f) (rename φ x) := by
  cases f with
  | ok f' =>
    cases x with
    | ok a =>
      simp only [ap_ok_ok, rename_ok]
      exact cast_ok _ _
    | err e he =>
      simp only [ap_ok_err, rename_err, rename_ok]
      rw [cast_err]
  | err e he =>
    simp only [ap_err_left, rename_err]
    rw [cast_err]

/-- `rename` commutes with `map2`, up to `Grade.rename_join`. -/
theorem rename_map2 (φ : Err → Err') (k : α → β → γ) (x : Graded g α) (y : Graded h β) :
    cast (Grade.rename_join φ g h) (rename φ (map2 k x y)) =
      map2 k (rename φ x) (rename φ y) := by
  simp only [map2]
  rw [rename_ap, rename_map]

/-- A graded monad morphism: a map on grades that is a join-semilattice
    homomorphism (`gmap_join`, `gmap_bot`), together with a family on
    carriers, natural at every grade and payload type, that commutes with
    `bind`, `pure`, and the subsumption conversion `widen`.

    **`hom_widen` was added by [morphism-bridge]**, and it is what makes
    `GradedHom.toGradedHomK` (`Graded/Sufficient.lean`) total. `widen` is
    a primitive of the carrier that `bind` and `pure` do not define, so
    `hom_bind`/`hom_pure` say nothing about how `hom` treats it; without
    this field the forward bridge to `GradedHomK` stops at `gmap_mono`,
    carrying `gmap`'s obligation and none of `hom`'s. It takes the target
    inclusion `h₂` as an argument rather than deriving it, because
    `gmap_mono` is a theorem proved from `gmap_join` *after* this
    structure exists — and it costs nothing to quantify over `h₂`, since
    `widen_irrel` is `rfl`. Every morphism anyone can actually write has
    this property; the point is that the record now says so. This is the definition of
    "graded morphism" the C++ design lacks — `renameHom` below packages
    `Grade.rename`/`rename` as the one instance the design actually uses.

    > **Provisional.** No field here asks `gmap`/`hom` to be injective or
    > surjective, and nothing in this file's proofs needed either: every
    > law (`gmap_join`, `gmap_bot`, `hom_bind`, `hom_pure`, and the
    > `traverse` naturality law below) goes through for an arbitrary `φ`,
    > including a many-to-one coarsening. Revisit only if a later
    > consumer needs to *recover* the source grade from the target one,
    > which would need injectivity, or needs every target grade hit,
    > which would need surjectivity — neither is needed here. -/
structure GradedHom (Err : Type u) (Err' : Type u) [DecidableEq Err] [DecidableEq Err'] where
  gmap : Grade Err → Grade Err'
  gmap_join : ∀ g h : Grade Err, gmap (Grade.join g h) = Grade.join (gmap g) (gmap h)
  gmap_bot : gmap (Grade.bot : Grade Err) = Grade.bot
  hom : ∀ {g : Grade Err} {α : Type v}, Graded g α → Graded (gmap g) α
  hom_bind : ∀ {g h : Grade Err} {α β : Type v} (x : Graded g α) (f : α → Graded h β),
      cast (gmap_join g h) (hom (bind x f)) = bind (hom x) (fun a => hom (f a))
  hom_pure : ∀ {α : Type v} (a : α),
      cast gmap_bot (hom (pure a : Graded (Grade.bot : Grade Err) α)) = pure a
  hom_widen : ∀ {g g' : Grade Err} {α : Type v} (h₁ : g ⊆ g')
      (h₂ : gmap g ⊆ gmap g') (x : Graded g α),
      hom (widen h₁ x) = widen h₂ (hom x)

/-- The one instance of `GradedHom` the C++ design uses: renaming error
    kinds along `φ`. -/
def renameHom (φ : Err → Err') : GradedHom Err Err' where
  gmap := Grade.rename φ
  gmap_join := Grade.rename_join φ
  gmap_bot := Grade.rename_bot φ
  hom := rename φ
  hom_bind := rename_bind φ
  hom_pure := rename_pure φ
  hom_widen := fun h₁ _h₂ x => rename_widen φ h₁ x

-- ---------------------------------------------------------------------
-- Naturality of `traverse` against `rename`: renaming after traversing
-- agrees with traversing the renamed element function. Unlike
-- `rename_bind`/`rename_ap`, no top-level cast is needed — `traverse`
-- fixes its result at the exact grade `g` (via `widen`, not `bind`'s
-- `join`), so both sides live at `Grade.rename φ g` outright. The casts
-- from `rename_cast`/`rename_map2`/`Grade.join_idem` are only needed
-- *inside* the induction step, to push `rename` through `traverse_cons`,
-- and cancel by proof irrelevance (`widen_irrel`'s reasoning: any two
-- proofs of the same grade equality are the same cast) rather than by an
-- extra rewrite.

theorem traverse_rename (φ : Err → Err') (f : α → Graded g β) (xs : List α) :
    rename φ (traverse f xs) = traverse (rename φ ∘ f) xs := by
  induction xs with
  | nil =>
    rw [traverse_nil, traverse_nil, fromEmpty_eq_ok, fromEmpty_eq_ok, rename_ok]
  | cons x xs ih =>
    rw [traverse_cons, traverse_cons, rename_cast, Function.comp_apply, ← ih, ← rename_map2,
      cast_cast]

-- ---------------------------------------------------------------------
-- `Accum` also admits `rename`, and `toGraded` commutes with it — kept
-- in scope (not dropped) because both the definition and the theorem
-- came out short: `Accum.rename` maps the error list through `φ`
-- elementwise, and `toGraded` (first error) doesn't care whether `φ` was
-- applied before or after picking the first element of a nonempty list.

namespace Accum

/-- Rename every error in an `Accum`'s list along `φ`: `ok` is untouched,
    `errs` maps `φ` over the whole list. Mirrors `Graded.rename`. -/
def rename (φ : Err → Err') : Accum g α → Accum (Grade.rename φ g) α
  | .ok a => .ok a
  | .errs es hne hmem =>
      .errs (es.map φ) (fun h => hne (List.map_eq_nil_iff.mp h))
        (fun _e he =>
          let ⟨e', he', heq⟩ := List.mem_map.mp he
          heq ▸ Grade.mem_rename (hmem e' he'))

/-- `toGraded` (first error) commutes with `rename`: renaming the whole
    list then taking its head agrees with taking the head then renaming
    it, since `φ` is applied elementwise and `(e :: es).map φ = φ e ::
    es.map φ` definitionally. -/
theorem rename_toGraded (φ : Err → Err') (x : Accum g α) :
    Graded.rename φ (toGraded x) = toGraded (Accum.rename φ x) := by
  cases x with
  | ok a => rfl
  | errs es hne hmem =>
    cases es with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl

end Accum

end Graded
