import Graded.Obligations
import Graded.Sufficient
import Graded.AccumTraverse

/-! The operational interfaces, abstract over the grade *and* the carrier.

    `Graded/Obligations.lean` states what a grade must be, and is consumed
    by nothing: four grades inhabit `PreorderedGradeMonoid` and no carrier
    module imports it. The abstraction and the model do not touch. This
    module connects them, and it is written as a **bet with an exit** —
    see `docs/design.md#abstract-operational-classes` for the criterion
    and for what was measured.

    **The sufficient-grade layer is the one worth abstracting.** Its laws
    compare terms in the same type and hide no transports: at a
    caller-nominated `k`, both sides of every law already live in `M k β`,
    so there is no grade equation for a `cast` to carry. The union-graded
    operations are recovered as derived conveniences using the two join
    inclusions, which is the direction the existing
    `bind_eq_bindK`/`ap_eq_apK` bridges already run.

    **One `pure`, on the functor.** `GradedMonadK` and `GradedApplicativeK`
    take `[GradedFunctorK G M]` as an instance *parameter* rather than
    extending it. A carrier with both — which `Graded` is — therefore has
    one `pure` and one route to the functor, not two of each needing a
    coherence law between them. `pureK` is derived once, below, as `pure`
    widened from `bot`; leaving a primitive `pureK` at every grade would
    let its behaviour depend on the nominated grade and would need exactly
    the coherence law this shape avoids.

    **`widen_irrel` is free here, and that is not an accident.** Which
    proof of `le g k` is supplied cannot affect `widen h x`, because `le g
    k` is a `Prop` and Lean's proof irrelevance is definitional. The
    concrete `widen_irrel`/`bindK_irrel`/`traverseK_irrel` are `rfl` for
    that reason, and the same holds of an abstract carrier nobody has
    inspected. No law states it because none has to. -/

namespace Graded.Effect

open PreorderedGradeMonoid

universe u v w

variable {G : Type u} {M F : G → Type v → Type w} {α β γ : Type v}

-- ---------------------------------------------------------------------
-- The three operational classes: data only. Laws live in the `Lawful*`
-- companions below, so a carrier can be given its operations and have
-- them checked separately, and so an instance that satisfies only some
-- laws is a statable thing rather than an impossible one.

/-- Mapping and subsumption at a fixed grade, plus `pure` at `bot`.
    `widen` is a primitive here for the same reason it is one in
    `Graded/Carrier.lean`: it is the carrier's own subsumption
    conversion, and neither `bindK` nor `apK` defines it. -/
class GradedFunctorK (G : Type u) (M : G → Type v → Type w)
    [PreorderedGradeMonoid G] where
  map : ∀ {g : G} {α β : Type v}, (α → β) → M g α → M g β
  widen : ∀ {g k : G} {α : Type v}, le g k → M g α → M k α
  pure : ∀ {α : Type v}, α → M (bot : G) α

/-- `pure` at any nominated grade, **derived, not primitive**: `pure` at
    `bot` widened up along `bot_le`. -/
def pureK [PreorderedGradeMonoid G] [GradedFunctorK G M] {k : G} (a : α) : M k α :=
  GradedFunctorK.widen (bot_le k) (GradedFunctorK.pure a)

/-- Sequencing into a continuation at a grade containing both sides. -/
class GradedMonadK (G : Type u) (M : G → Type v → Type w)
    [PreorderedGradeMonoid G] [GradedFunctorK G M] where
  bindK : ∀ {g h k : G} {α β : Type v}, le g k → le h k → M g α → (α → M h β) → M k β

/-- Applying a graded function to a graded argument at a grade containing
    both. **Not derived from `GradedMonadK`**: `Accum` instantiates this
    and has no monad instance at all (`Accum.notMonad`), and the
    difference is entirely in the case where both sides fail. -/
class GradedApplicativeK (G : Type u) (F : G → Type v → Type w)
    [PreorderedGradeMonoid G] [GradedFunctorK G F] where
  apK : ∀ {g h k : G} {α β : Type v}, le g k → le h k → F g (α → β) → F h α → F k β

-- ---------------------------------------------------------------------
-- The laws, as separate `Prop` classes. Each statement is the concrete
-- one from `Graded/Sufficient.lean` with `Finset` erased: same shape,
-- same hypotheses, no `cast` anywhere.

-- Class projections are written out in full below rather than brought
-- into scope with `open`. Inside `namespace Graded.Effect` the concrete
-- `Graded.map`/`Graded.widen` are already visible, and an `open
-- GradedFunctorK` does not displace them — the statements silently
-- elaborate against the concrete carrier and fail with a type mismatch
-- on an abstract one. Qualifying is also the citation discipline
-- `docs/RULES.md` asks for everywhere else.

class LawfulGradedFunctorK (G : Type u) (M : G → Type v → Type w)
    [PreorderedGradeMonoid G] [GradedFunctorK G M] : Prop where
  map_id : ∀ {g : G} {α : Type v} (x : M g α), GradedFunctorK.map id x = x
  map_comp : ∀ {g : G} {α β γ : Type v} (f : α → β) (h : β → γ) (x : M g α),
      GradedFunctorK.map (h ∘ f) x = GradedFunctorK.map h (GradedFunctorK.map f x)
  widen_widen : ∀ {g g' k : G} {α : Type v} (h₁ : le g g') (h₂ : le g' k) (x : M g α),
      GradedFunctorK.widen h₂ (GradedFunctorK.widen h₁ x)
        = GradedFunctorK.widen (le_trans' h₁ h₂) x
  widen_map : ∀ {g k : G} {α β : Type v} (h₁ : le g k) (f : α → β) (x : M g α),
      GradedFunctorK.widen h₁ (GradedFunctorK.map f x)
        = GradedFunctorK.map f (GradedFunctorK.widen h₁ x)
  /-- `map` over a `pure` is `pure` of the mapped value. Stated at `bot`,
      where `pure` lives; `map_pureK` below carries it to every grade
      using `widen_map`, so this is the only coherence between `map` and
      `pure` a carrier has to supply. -/
  map_pure : ∀ {α β : Type v} (f : α → β) (a : α),
      GradedFunctorK.map f (GradedFunctorK.pure a : M (bot : G) α)
        = GradedFunctorK.pure (f a)

class LawfulGradedMonadK (G : Type u) (M : G → Type v → Type w)
    [PreorderedGradeMonoid G] [GradedFunctorK G M] [GradedMonadK G M] : Prop where
  bindK_pure_left : ∀ {h k : G} {α β : Type v} (hh : le h k) (a : α) (f : α → M h β),
      GradedMonadK.bindK (bot_le k) hh (GradedFunctorK.pure a) f
        = GradedFunctorK.widen hh (f a)
  bindK_pure_right : ∀ {g k : G} {α : Type v} (hg : le g k) (x : M g α),
      GradedMonadK.bindK hg (bot_le k) x GradedFunctorK.pure
        = GradedFunctorK.widen hg x
  bindK_assoc : ∀ {g h j k : G} {α β γ : Type v}
      (hg : le g k) (hh : le h k) (hj : le j k)
      (x : M g α) (f : α → M h β) (kk : β → M j γ),
      GradedMonadK.bindK (le_refl' k) hj (GradedMonadK.bindK hg hh x f) kk
        = GradedMonadK.bindK hg (le_refl' k) x (fun a => GradedMonadK.bindK hh hj (f a) kk)
  bindK_widen : ∀ {g g' h k : G} {α β : Type v}
      (h₁ : le g g') (hg' : le g' k) (hh : le h k) (x : M g α) (f : α → M h β),
      GradedMonadK.bindK hg' hh (GradedFunctorK.widen h₁ x) f
        = GradedMonadK.bindK (le_trans' h₁ hg') hh x f

class LawfulGradedApplicativeK (G : Type u) (F : G → Type v → Type w)
    [PreorderedGradeMonoid G] [GradedFunctorK G F] [GradedApplicativeK G F] : Prop where
  apK_pure_id : ∀ {h k : G} {α : Type v} (hh : le h k) (x : F h α),
      GradedApplicativeK.apK (le_refl' k) hh (pureK (@id α)) x
        = GradedFunctorK.widen hh x
  apK_pure_pure : ∀ {k : G} {α β : Type v} (f : α → β) (a : α),
      GradedApplicativeK.apK (le_refl' k) (le_refl' k) (pureK f) (pureK a)
        = (pureK (f a) : F k β)
  apK_interchange : ∀ {g k : G} {α β : Type v} (hg : le g k) (u : F g (α → β)) (a : α),
      GradedApplicativeK.apK hg (le_refl' k) u (pureK a)
        = GradedApplicativeK.apK (le_refl' k) hg (pureK (fun f => f a)) u
  apK_comp : ∀ {g g' j k : G} {α β γ : Type v}
      (hg : le g k) (hg' : le g' k) (hj : le j k)
      (u : F g (β → γ)) (v : F g' (α → β)) (w : F j α),
      GradedApplicativeK.apK (le_refl' k) hj
          (GradedApplicativeK.apK (le_refl' k) hg'
            (GradedApplicativeK.apK (le_refl' k) hg (pureK Function.comp) u) v) w
        = GradedApplicativeK.apK hg (le_refl' k) u (GradedApplicativeK.apK hg' hj v w)

-- ---------------------------------------------------------------------
-- Derived generic facts, proved once from the law classes and available
-- at every carrier that instantiates them.

section Derived
variable [PreorderedGradeMonoid G] [GradedFunctorK G M] [LawfulGradedFunctorK G M]

/-- `map` over `pureK` at *any* grade, not only at `bot`: `map_pure`
    carried up by `widen_map`. This is why `map_pure` is the only
    `map`/`pure` coherence a carrier has to state. -/
theorem map_pureK {k : G} (f : α → β) (a : α) :
    GradedFunctorK.map f (pureK a : M k α) = pureK (f a) := by
  rw [pureK, ← LawfulGradedFunctorK.widen_map, LawfulGradedFunctorK.map_pure, pureK]

end Derived

-- ---------------------------------------------------------------------
-- List traversal, defined **once**, over any graded applicative. The
-- concrete `Graded.traverseK` and `Graded.Accum.traverseK` are this
-- definition at two carriers, and `traverseGK_eq_*` below say so.
--
-- As at [sufficient-grade-traverse], there is no fold: the caller
-- nominates `k`, one inclusion `hg` is reused at every position, and the
-- result type is `F k (List β)` for every list regardless of length. So
-- length-independence is a property of the signature here too, and needs
-- no idempotence — which is the point of stating it generically, since
-- the abstract `G` is only a *preordered* grade monoid and has no
-- idempotence to spend.

section Traverse
variable [PreorderedGradeMonoid G] [GradedFunctorK G F] [GradedApplicativeK G F]

/-- Traverse a list with a graded effect, landing at the caller's grade. -/
def traverseGK {g k : G} (hg : le g k) (f : α → F g β) : List α → F k (List β)
  | []      => pureK []
  | x :: xs => GradedApplicativeK.apK hg (le_refl' k)
      (GradedFunctorK.map (fun b bs => b :: bs) (f x)) (traverseGK hg f xs)

theorem traverseGK_nil {g k : G} (hg : le g k) (f : α → F g β) :
    traverseGK hg f ([] : List α) = pureK [] := rfl

theorem traverseGK_cons {g k : G} (hg : le g k) (f : α → F g β) (x : α) (xs : List α) :
    traverseGK hg f (x :: xs)
      = GradedApplicativeK.apK hg (le_refl' k)
          (GradedFunctorK.map (fun b bs => b :: bs) (f x)) (traverseGK hg f xs) := rfl

/-- **Source `map` fusion**, at the polymorphic layer: reindexing the
    input before traversing agrees with traversing the reindexed
    function. Needs no law at all — it is induction over the two
    reduction lemmas, and both are `rfl`. -/
theorem traverseGK_map {g k : G} (hg : le g k) (f : α → F g β) (h : γ → α) (xs : List γ) :
    traverseGK hg f (xs.map h) = traverseGK hg (f ∘ h) xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      change traverseGK hg f (h y :: ys.map h) = traverseGK hg (f ∘ h) (y :: ys)
      rw [traverseGK_cons, traverseGK_cons, ih]
      rfl

variable [LawfulGradedFunctorK G F] [LawfulGradedApplicativeK G F]

/-- **The identity law**: traversing with a context that cannot fail is
    the identity. This is the first theorem in this module whose proof
    actually spends the law classes — `map_pureK` to push the cons
    through `pureK`, then `apK_pure_pure` to combine two `pureK`s. -/
theorem traverseGK_pureK {k : G} (xs : List α) :
    traverseGK (le_refl' k) (fun a => (pureK a : F k α)) xs = pureK xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      rw [traverseGK_cons, ih, map_pureK, LawfulGradedApplicativeK.apK_pure_pure]

end Traverse

-- ---------------------------------------------------------------------
-- The instances. Every field is an existing definition or an existing
-- theorem, cited by name: the point of this layer is to *connect* the
-- abstraction to the model, so a proof that had to be redone here would
-- be evidence the abstraction had drifted from what the model proves.

variable {Err : Type u} [DecidableEq Err]

instance instGradedFunctorKGraded :
    GradedFunctorK (Grade Err) (Graded.Graded (Err := Err)) where
  map := Graded.map
  widen := Graded.widen
  pure := Graded.pure

instance instGradedMonadKGraded :
    GradedMonadK (Grade Err) (Graded.Graded (Err := Err)) where
  bindK := Graded.bindK

instance instGradedApplicativeKGraded :
    GradedApplicativeK (Grade Err) (Graded.Graded (Err := Err)) where
  apK := Graded.apK

instance instLawfulGradedFunctorKGraded :
    LawfulGradedFunctorK (Grade Err) (Graded.Graded (Err := Err)) where
  map_id := Graded.map_id
  map_comp := Graded.map_comp
  widen_widen := Graded.widen_widen
  widen_map := Graded.widen_map
  map_pure := fun _ _ => rfl

instance instLawfulGradedApplicativeKGraded :
    LawfulGradedApplicativeK (Grade Err) (Graded.Graded (Err := Err)) where
  apK_pure_id := Graded.apK_pure_id
  apK_pure_pure := Graded.apK_pure_pure
  apK_interchange := Graded.apK_interchange
  apK_comp := Graded.apK_comp

instance instLawfulGradedMonadKGraded :
    LawfulGradedMonadK (Grade Err) (Graded.Graded (Err := Err)) where
  bindK_pure_left := Graded.bindK_pure_left
  bindK_pure_right := Graded.bindK_pure_right
  bindK_assoc := Graded.bindK_assoc
  bindK_widen := Graded.bindK_widen

-- ---------------------------------------------------------------------
-- `Accum`: applicative, and **no** `GradedMonadK` instance. There is no
-- `instGradedMonadKAccum` anywhere in this file, and there cannot be:
-- `Graded.Accum.notMonad` proves no `bind` reproduces `Accum.ap`, because
-- a monad's sequencing cannot keep both sides' errors. That absence is
-- why the applicative is its own class here rather than a derived
-- consequence of the monad, and why `GradedApplicativeK` takes the
-- functor as a parameter instead of extending a monad class.

instance instGradedFunctorKAccum :
    GradedFunctorK (Grade Err) (Graded.Accum (Err := Err)) where
  map := Graded.Accum.map
  widen := Graded.Accum.widen
  pure := Graded.Accum.pure

instance instGradedApplicativeKAccum :
    GradedApplicativeK (Grade Err) (Graded.Accum (Err := Err)) where
  apK := Graded.Accum.apK

instance instLawfulGradedFunctorKAccum :
    LawfulGradedFunctorK (Grade Err) (Graded.Accum (Err := Err)) where
  map_id := Graded.Accum.map_id
  map_comp := Graded.Accum.map_comp
  widen_widen := Graded.Accum.widen_widen
  widen_map := Graded.Accum.widen_map
  map_pure := fun _ _ => rfl

instance instLawfulGradedApplicativeKAccum :
    LawfulGradedApplicativeK (Grade Err) (Graded.Accum (Err := Err)) where
  apK_pure_id := Graded.Accum.apK_pure_id
  apK_pure_pure := Graded.Accum.apK_pure_pure
  apK_interchange := Graded.Accum.apK_interchange
  apK_comp := Graded.Accum.apK_comp

-- ---------------------------------------------------------------------
-- The third carrier: the product-graded composite. `Comp g h α` is
-- graded by a *pair*, which is why it never fitted a class indexed by
-- one grade — until `Graded.instPreorderedGradeMonoidProd` made a pair
-- of grades a grade. With that, `Comp` is an instance of the same
-- interface as the other two, and `traverseGK` reaches all three.
--
-- Data only, deliberately. `Comp` has `map_id`/`map_comp` and the `apK`
-- reduction lemmas and `apK_interchange`, but `widen_widen`, `widen_map`,
-- `map_pure`, `apK_pure_id`, `apK_pure_pure` and `apK_comp` do not exist
-- for it at the sufficient grade, and inventing six lemmas to fill a
-- `Lawful` instance is a different piece of work from connecting the
-- abstraction. `traverseGK` needs only the data classes, so it
-- instantiates here regardless; what is missing is the *laws* about it,
-- and `docs/design.md#abstract-operational-classes` says so rather than
-- leaving the absence to be discovered.

/-- The composite carrier, re-indexed by a single product grade.

    Note the payload universe: `Graded.Comp` is declared
    `(α : Type u) : Type u` with `u` the *error* type's universe, so the
    composite only exists where payload and error live at the same level.
    That is a pre-existing collapse in `Graded/ComposeApp.lean`, not
    something this instance introduces, but it is why `CompP` cannot be
    stated at an independent payload universe the way `Graded` and
    `Accum` can. -/
abbrev CompP (Err : Type u) [DecidableEq Err]
    (p : Grade Err × Grade Err) (α : Type u) : Type u :=
  Graded.Comp p.1 p.2 α

instance instGradedFunctorKComp :
    GradedFunctorK (Grade Err × Grade Err) (CompP Err) where
  map := Graded.Comp.map
  widen := fun h x => Graded.Comp.widenGH h.1 h.2 x
  pure := Graded.Comp.pure

instance instGradedApplicativeKComp :
    GradedApplicativeK (Grade Err × Grade Err) (CompP Err) where
  apK := fun hg hh u v => Graded.Comp.apK hg.1 hh.1 hg.2 hh.2 u v

-- ---------------------------------------------------------------------
-- The two concrete traversals *are* the generic one. Both by `rfl`:
-- `traverseK`'s cons case is `map2K`, `map2K` is `apK` after `map`, and
-- that is exactly `traverseGK`'s cons case.

theorem traverseGK_eq_traverseK {g k : Grade Err} (hg : g ⊆ k)
    (f : α → Graded.Graded g β) (xs : List α) :
    traverseGK hg f xs = Graded.traverseK hg f xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [traverseGK_cons, Graded.traverseK_cons, ih]; rfl

theorem traverseGK_eq_accum_traverseK {g k : Grade Err} (hg : g ⊆ k)
    (f : α → Graded.Accum g β) (xs : List α) :
    traverseGK hg f xs = Graded.Accum.traverseK hg f xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [traverseGK_cons, Graded.Accum.traverseK_cons, ih]; rfl

-- ---------------------------------------------------------------------
-- Transformations between graded applicatives, and traversal naturality
-- proved once for all of them.
--
-- This is the piece that pays for the abstraction rather than merely
-- organising it. `Graded.Accum.toGraded_traverseK` ([accum-traverse]) is
-- a theorem about one projection between two named carriers, proved by
-- its own induction. Below, it is `app_traverseGK` — a generic law —
-- instantiated at one transformation, and the induction happens once.

/-- A transformation between graded applicatives over the same grade:
    natural in the payload, and commuting with `map`, `pure`, `widen`
    and `apK`. The `widen` field is the one an ordinary applicative
    transformation does not have, and it is needed for the same reason
    `GradedHom.hom_widen` is ([morphism-bridge]): subsumption is a
    primitive of a graded carrier that the other operations do not
    define. -/
structure ApplicativeTransformationK (G : Type u) (F F' : G → Type v → Type w)
    [PreorderedGradeMonoid G] [GradedFunctorK G F] [GradedFunctorK G F']
    [GradedApplicativeK G F] [GradedApplicativeK G F'] where
  app : ∀ {g : G} {α : Type v}, F g α → F' g α
  app_map : ∀ {g : G} {α β : Type v} (f : α → β) (x : F g α),
      app (GradedFunctorK.map f x) = GradedFunctorK.map f (app x)
  app_pure : ∀ {α : Type v} (a : α),
      app (GradedFunctorK.pure a : F (bot : G) α) = GradedFunctorK.pure a
  app_widen : ∀ {g k : G} {α : Type v} (h : le g k) (x : F g α),
      app (GradedFunctorK.widen h x) = GradedFunctorK.widen h (app x)
  app_apK : ∀ {g h k : G} {α β : Type v} (hg : le g k) (hh : le h k)
      (u : F g (α → β)) (v : F h α),
      app (GradedApplicativeK.apK hg hh u v)
        = GradedApplicativeK.apK hg hh (app u) (app v)

namespace ApplicativeTransformationK
variable [PreorderedGradeMonoid G] [GradedFunctorK G F] [GradedFunctorK G M]
variable [GradedApplicativeK G F] [GradedApplicativeK G M]

/-- `pureK` at any grade is preserved: `app_pure` carried up by
    `app_widen`, the same two-step `map_pureK` uses. -/
theorem app_pureK (T : ApplicativeTransformationK G F M) {k : G} (a : α) :
    T.app (pureK a : F k α) = pureK a := by
  rw [pureK, T.app_widen, T.app_pure, pureK]

/-- **Traversal naturality, proved once.** Transform after traversing, or
    transform each element and then traverse: the same value. Every
    instance of this — first-error projection, error renaming, a change
    of representation — is this theorem rather than its own induction. -/
theorem app_traverseGK (T : ApplicativeTransformationK G F M) {g k : G}
    (hg : le g k) (f : α → F g β) (xs : List α) :
    T.app (traverseGK hg f xs) = traverseGK hg (fun a => T.app (f a)) xs := by
  induction xs with
  | nil => exact T.app_pureK []
  | cons y ys ih =>
      rw [traverseGK_cons, T.app_apK, T.app_map, ih, traverseGK_cons]

end ApplicativeTransformationK

-- ---------------------------------------------------------------------
-- `Accum.toGraded` is such a transformation, and [accum-traverse]'s
-- headline theorem is the generic law at it.

/-- Taking the first error is a graded applicative transformation from
    the accumulating carrier to the short-circuiting one. Every field
    cites a theorem `Graded/AccumTraverse.lean` already proves. -/
def toGradedTransformation :
    ApplicativeTransformationK (Grade Err) (Graded.Accum (Err := Err))
      (Graded.Graded (Err := Err)) where
  app := Graded.Accum.toGraded
  app_map := Graded.Accum.toGraded_map
  app_pure := fun _ => rfl
  app_widen := Graded.Accum.toGraded_widen
  app_apK := Graded.Accum.toGraded_apK

/-- [accum-traverse]'s `toGraded_traverseK`, recovered as the generic
    naturality law at one transformation. The concrete theorem keeps its
    own induction and its own name; this is the statement that the
    induction did not have to be written twice. -/
theorem toGraded_traverseK_generic {g k : Grade Err} (hg : g ⊆ k)
    (f : α → Graded.Accum g β) (xs : List α) :
    Graded.Accum.toGraded (Graded.Accum.traverseK hg f xs)
      = Graded.traverseK hg (fun a => Graded.Accum.toGraded (f a)) xs := by
  rw [← traverseGK_eq_accum_traverseK, ← traverseGK_eq_traverseK]
  exact toGradedTransformation.app_traverseGK hg f xs

end Graded.Effect
