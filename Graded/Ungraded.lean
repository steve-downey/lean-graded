import Graded.Monad
import Graded.Applicative
import Graded.Traverse

/-! The comparison column: what a monad/applicative/traversal law costs at
    all, against what grading adds on top. Every step until now recorded
    only one number — the pomonoid property each law's *proof* consumes —
    and that number silently conflates two different questions. This
    module answers the second one directly, by fixing a single grade `g`
    and writing the *same* laws down again with no grade arithmetic in
    their statements at all.

    **The construction.** `Fixed g α` is not a new type: it is `Graded g α`
    read with the grade held still ([carrier](../docs/design.md#carrier)).
    `pureF` reuses `fromEmpty` ([subsumption](../docs/design.md#subsumption))
    rather than going through `Grade.bot` — a fixed-grade `pure` has
    nowhere else to land. `bindF`/`apF`/`map2F` reuse `bind`/`ap`/`map2`
    ([monad](../docs/design.md#monad), [applicative](../docs/design.md#applicative))
    and immediately collapse the one `join g g` each produces, via
    `Grade.join_idem`, back down to `g`. `traverse` itself needs no such
    wrapper: [traverse-list] already built it uniform in one grade
    throughout ([traverse](../docs/design.md#traverse)), so `Fixed`'s
    traversal *is* `Graded.traverse`, unchanged.

    **The result.** `bindF_pure_left`, `bindF_pure_right`, `bindF_assoc`,
    and the four `apF_*` laws below are the ordinary monad and applicative
    laws, verbatim — no `cast`, no `join`, nothing about grades in any
    statement. Their *proofs* still cite `Grade.join_idem` throughout
    (nothing here is free), but never the unit or associativity properties
    the general `bind`/`ap` laws needed: `pureF` is already at grade `g`,
    not at `⊥`, so there is no `bot_join`/`join_bot` left to pay for, and
    `bindF_assoc`'s proof needs no `Grade.join_assoc` either — see that
    theorem's docstring for why. This is precisely the second column: what
    survives once a single grade is held fixed is exactly what grading
    adds, read backwards. -/

namespace Graded
variable {Err : Type u} [DecidableEq Err] {g : Grade Err}
variable {α β γ : Type v}

/-- The carrier at one fixed grade. Not a new type: a reading of the
    existing `Graded g α` with the grade held still. `abbrev`, not `def`,
    so instance search (`DecidableEq`, used by the tests) sees straight
    through it, exactly as `Grade` itself is an `abbrev` for the same
    reason ([carrier](../docs/design.md#carrier)'s `Comp` note applies
    here too). -/
abbrev Fixed (g : Grade Err) (α : Type v) : Type (max u v) := Graded g α

/-- `pure` into a fixed grade, through the ∅-collapse and widened up to
    `g` — `fromEmpty` from [subsumption-widen], reused, not redefined.
    There is no `Grade.bot` anywhere in `Fixed`'s vocabulary for a
    fixed-grade `pure` to land at instead. -/
def pureF (a : α) : Fixed g α := fromEmpty a

theorem pureF_eq_ok (a : α) : (pureF a : Fixed g α) = Graded.ok a :=
  fromEmpty_eq_ok a

/-- `bind` at one fixed grade: the union `g ⊔ g` collapses to `g` by
    `Grade.join_idem`, the one property this whole module spends
    everywhere. -/
def bindF (x : Fixed g α) (f : α → Fixed g β) : Fixed g β :=
  cast (Grade.join_idem g) (bind x f)

/-- **Reduction lemma, not a law.** `bindF` on an `ok` value is exactly
    the continuation — the same collapse `bind_pure_left` exploits, but
    for an arbitrary continuation `f`, not only `pure`'s. Every later law
    in this file is proved by reducing to this and `bindF_err` rather than
    re-deriving the `cast`/`widen` shuffle each time. -/
theorem bindF_ok (a : α) (f : α → Fixed g β) : bindF (Graded.ok a : Fixed g α) f = f a := by
  simp only [bindF, bind]
  rw [cast_widen]
  exact widen_refl (f a)

/-- **Reduction lemma, not a law.** `bindF` on an `err` value ignores the
    continuation entirely, exactly as `bind` itself does. -/
theorem bindF_err (e : Err) (he : e ∈ g) (f : α → Fixed g β) :
    bindF (Graded.err e he : Fixed g α) f = Graded.err e he := by
  simp only [bindF, bind]
  rw [cast_err]

/-- (unit, in the general law; here: idempotence only) `pure` on the left
    of `bindF` is the continuation itself — no grade arithmetic in sight,
    unlike `bind_pure_left`'s `cast (Grade.bot_join h)`. -/
theorem bindF_pure_left (a : α) (f : α → Fixed g β) : bindF (pureF a) f = f a := by
  rw [pureF_eq_ok]
  exact bindF_ok a f

/-- (unit, in the general law; here: idempotence only) `pure` on the right
    of `bindF` is the original value. -/
theorem bindF_pure_right (x : Fixed g α) : bindF x (pureF : α → Fixed g α) = x := by
  cases x using Graded.rec' with
  | ok a => exact bindF_ok a pureF
  | err e he => exact bindF_err e he pureF

/-- (associative, in the general law; here: idempotence only, and only
    once per `bindF`, never `Grade.join_assoc`) `bindF` re-associates,
    with no cast anywhere in the statement. The general `bind_assoc` needs
    associativity because three *different* grades' union has two ways to
    parenthesize; here every grade is the same `g`, so `bindF_ok`/
    `bindF_err` already reduce both sides to the same term before any
    question of associativity could arise — the property that vanishes
    from `bind_assoc`'s proof at a fixed grade is `Grade.join_assoc`
    itself, not merely its appearance in the statement. -/
theorem bindF_assoc (x : Fixed g α) (f : α → Fixed g β) (k : β → Fixed g γ) :
    bindF (bindF x f) k = bindF x (fun a => bindF (f a) k) := by
  cases x using Graded.rec' with
  | ok a => rw [bindF_ok a f, bindF_ok a (fun a => bindF (f a) k)]
  | err e he => rw [bindF_err e he f, bindF_err e he k, bindF_err e he (fun a => bindF (f a) k)]

/-- `ap` at one fixed grade, collapsed by `Grade.join_idem` exactly as
    `bindF` is. -/
def apF (f : Fixed g (α → β)) (x : Fixed g α) : Fixed g β :=
  cast (Grade.join_idem g) (ap f x)

/-- `map2` at one fixed grade, the same collapse. No separate laws are
    stated for it, for the same reason none are stated for `Graded.map2`
    on its own: every law `map2F` would need is `apF`'s, transported
    through `ap`'s own definition in terms of `bind`. -/
def map2F (k : α → β → γ) (x : Fixed g α) (y : Fixed g β) : Fixed g γ :=
  cast (Grade.join_idem g) (map2 k x y)

-- ---------------------------------------------------------------------
-- Reduction lemmas: how `apF` computes on each combination of
-- constructors, exactly as `Applicative`'s `ap_ok_ok`/`ap_err_left`/
-- `ap_ok_err` do for `ap`. Not laws in their own right; the four laws
-- below are proved from these.

theorem apF_ok_ok (f' : α → β) (a : α) :
    apF (Graded.ok f' : Fixed g (α → β)) (Graded.ok a : Fixed g α) = Graded.ok (f' a) := by
  simp only [apF, ap_ok_ok]
  rw [cast_ok]

theorem apF_err_left (e : Err) (he : e ∈ g) (x : Fixed g α) :
    apF (Graded.err e he : Fixed g (α → β)) x = Graded.err e he := by
  simp only [apF, ap_err_left]
  rw [cast_err]

theorem apF_ok_err (f' : α → β) (e : Err) (he : e ∈ g) :
    apF (Graded.ok f' : Fixed g (α → β)) (Graded.err e he : Fixed g α) = Graded.err e he := by
  simp only [apF, ap_ok_err]
  rw [cast_err]

-- ---------------------------------------------------------------------
-- The four applicative laws, cast-free in their statements. Each is the
-- corresponding `ap_*` law with every `Grade.bot`/unit property gone: a
-- fixed-grade `pureF` never touches `⊥`, so there is nothing left for the
-- unit laws to transport. Only `Grade.join_idem`, via the reduction
-- lemmas above, remains.

/-- (identity; general law: unit) Applying `pureF id` is the identity. -/
theorem apF_pure_id (x : Fixed g α) : apF (pureF (@id α)) x = x := by
  cases x using Graded.rec' with
  | ok a => exact apF_ok_ok id a
  | err e he => exact apF_ok_err id e he

/-- (homomorphism; general law: unit) Applying a `pureF` function to a
    `pureF` argument is the `pureF` of the application. -/
theorem apF_pure_pure (f : α → β) (a : α) :
    apF (pureF f : Fixed g (α → β)) (pureF a : Fixed g α) = (pureF (f a) : Fixed g β) :=
  apF_ok_ok f a

/-- (interchange; general law: unit, twice) Applying `u` to a `pureF`
    argument agrees with applying `pureF (· a)` to `u`. -/
theorem apF_interchange (u : Fixed g (α → β)) (a : α) :
    apF u (pureF a : Fixed g α) =
      apF (pureF (fun f => f a) : Fixed g ((α → β) → β)) u := by
  cases u using Graded.rec' with
  | ok f' => exact (apF_ok_ok f' a).trans (apF_ok_ok (fun f => f a) f').symm
  | err e he =>
      exact (apF_err_left e he (pureF a)).trans
        (apF_ok_err (fun f => f a : (α → β) → β) e he).symm

/-- (composition; general law: unit + associative) `apF` re-associates
    through `pureF (· ∘ ·)`, with no cast anywhere — the general `ap_comp`
    needs `Grade.bot_join` (to drop `pure`'s leading `∅`) and
    `Grade.join_assoc`; here `pureF` starts at `g`, not `∅`, and every
    grade is already the same `g`, so neither survives. -/
theorem apF_comp (u : Fixed g (β → γ)) (v : Fixed g (α → β)) (w : Fixed g α) :
    apF (apF (apF (pureF Function.comp :
        Fixed g ((β → γ) → (α → β) → α → γ)) u) v) w = apF u (apF v w) := by
  cases u using Graded.rec' with
  | err e he => simp only [pureF_eq_ok, apF_ok_err, apF_err_left]
  | ok f =>
    cases v using Graded.rec' with
    | err e he => simp only [pureF_eq_ok, apF_ok_ok, apF_ok_err, apF_err_left]
    | ok k =>
      cases w using Graded.rec' with
      | err e he => simp only [pureF_eq_ok, apF_ok_ok, apF_ok_err]
      | ok a => simp only [pureF_eq_ok, apF_ok_ok, Function.comp_apply]

/-! **A finding this module's proofs did not expect to make, recorded here
    rather than as a theorem**: `ap_flip`'s "at most one side is an error"
    hypothesis ([applicative](../docs/design.md#applicative)) is not a cost
    of grading at all. At a fixed grade the *grade*-level obstruction
    `ap_flip` needs `Grade.join_comm` for — comparing `Grade.join g h`
    against `Grade.join h g` — becomes a comparison of `Grade.join g g`
    against itself, trivial by proof irrelevance with no property cited.
    But the *value*-level disagreement (which of two failing sides a
    caller sees) is a fact about which argument an applicative sequences
    first, entirely independent of any grade arithmetic; it survives
    completely unchanged at a fixed grade, and would survive just as
    unchanged in a plain ungraded `Sum`/`Either`-shaped applicative with
    two independent failing computations. Not formalised as `apFlippedF`
    here — outside this step's declared scope — but nothing about the
    argument above depends on a grade ever changing. -/

/-! **`traverse` needs no fixed-grade specialization.** [traverse-list]
    already defined `Graded.traverse` uniform in one grade `g` throughout
    (via `widen` along `foldGrade_le`, never a `cast` that would need
    collapsing to a single grade after the fact) — there is no
    `traverseF` to write, because `traverse` already *is* its own
    fixed-grade form. The one new fact this module adds about it is a
    Mathlib correspondence, `traverse_fromEmpty_map` below, not a
    specialization. -/

/-- Mathlib's `LawfulTraversable.traverse_eq_map_id` analogue: traversing
    with `fromEmpty ∘ f` — an error-free embedding of `f` — agrees with
    mapping `f` over the list first and then embedding the whole result
    error-free. Not stated in `Graded/Traverse.lean` itself (out of this
    step's declared file scope); it follows in two steps from theorems
    already there — `traverse_map` (reindexing the source) and
    `traverse_fromEmpty` (traversing with an error-free identity is the
    identity) — so it costs nothing beyond citing both. -/
theorem traverse_fromEmpty_map (f : α → β) (xs : List α) :
    traverse (fromEmpty ∘ f : α → Graded g β) xs = fromEmpty (xs.map f) :=
  (traverse_map fromEmpty f xs).symm.trans (traverse_fromEmpty (xs.map f))

-- ---------------------------------------------------------------------
-- The correspondence with Mathlib's ungraded carrier. `Fixed g α` is not
-- literally `Sum Err α`: an `err` doesn't just carry an `Err`, it carries
-- an `Err` together with a proof of its membership in `g`. The honest
-- ungraded counterpart is `Sum {e : Err // e ∈ g} α`
-- (`Mathlib.Control.Traversable.Instances`'s `Sum.traverse`,
-- `Mathlib.Control.Basic`'s `Monad (Sum e)`), and the transport below is
-- an `Equiv` to that, not to `Sum Err α` outright.

/-- `Fixed g α` read as a Mathlib `Sum`: an `err`'s payload is the error
    together with its membership proof, bundled as the subtype Mathlib's
    `σ` is instantiated at; an `ok`'s payload is untouched. -/
def toSum (x : Fixed g α) : {e : Err // e ∈ g} ⊕ α :=
  match x with
  | .ok a => .inr a
  | .err e he => .inl ⟨e, he⟩

/-- The inverse of `toSum`. -/
def ofSum : ({e : Err // e ∈ g} ⊕ α) → Fixed g α
  | .inl e => Graded.err e.1 e.2
  | .inr a => Graded.ok a

/-- `Fixed g α ≃ {e : Err // e ∈ g} ⊕ α` — the ungraded carrier Mathlib
    already has `LawfulTraversable`/`LawfulMonad` instances for
    ([carrier](../docs/design.md#carrier)'s `emptyEquiv` is the same move,
    one grade earlier: an honest `Equiv`, not an identity). -/
def sumEquiv : Fixed g α ≃ ({e : Err // e ∈ g} ⊕ α) where
  toFun := toSum
  invFun := ofSum
  left_inv x := by cases x with
    | ok a => rfl
    | err e he => rfl
  right_inv x := by cases x with
    | inl e => obtain ⟨e, he⟩ := e; rfl
    | inr a => rfl

/-- `pureF` corresponds to `Sum`'s own `pure` (`Sum.inr`,
    `Mathlib.Control.Basic`'s `Monad (Sum e)` instance). -/
theorem sumEquiv_pureF (a : α) : sumEquiv (pureF a : Fixed g α) = Sum.inr a := by
  rw [pureF_eq_ok]; rfl

/-- `bindF` corresponds to `Sum`'s own `bind` (`Sum.bind`,
    `Mathlib.Control.Basic`): transporting through `sumEquiv` before or
    after binding agrees. Mathlib's `Sum.bind` short-circuits on `inl`
    exactly as `bindF_err` does on `err`, and hands the payload to the
    continuation on `inr` exactly as `bindF_ok` does on `ok` — the two are
    the same operation up to `sumEquiv`, not merely two operations with
    matching types. -/
theorem sumEquiv_bindF (x : Fixed g α) (f : α → Fixed g β) :
    sumEquiv (bindF x f) = Sum.bind (sumEquiv x) (fun a => sumEquiv (f a)) := by
  cases x using Graded.rec' with
  | ok a =>
    change toSum (bindF (Graded.ok a) f) = Sum.bind (toSum (Graded.ok a : Fixed g α)) _
    rw [bindF_ok]
    rfl
  | err e he =>
    change toSum (bindF (Graded.err e he) f) = Sum.bind (toSum (Graded.err e he : Fixed g α)) _
    rw [bindF_err]
    rfl

end Graded
