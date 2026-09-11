import Graded.Grade

/-! What a grade has to be, stated as an obligation rather than an
    observation. `docs/design.md#cpp-counterpart` ends: "Only `error_set` is
    intended as a grade for now; the design should not make it the only
    possible grade." Fourteen prior steps each recorded which pomonoid
    property a law consumed, but `Graded.Grade Err` is a concrete `abbrev`
    for `Finset Err`, so nothing ever forced a proof to live inside its
    recorded budget, and no second grade was ever tried.

    This module states the budget as one operational class and four
    independent `Prop` mixins over it, each **parameterised by** that
    class rather than extending it.

    - `PreorderedGradeMonoid` — associative join, a two-sided unit, a
      preorder with `bot` as its minimum, and monotonicity of `join` in
      the order. **This is the operational obligation**: every monad,
      applicative, traversal, subsumption and morphism law in `Graded/`
      needs at most this, per [obligation-layering]'s classification. The
      name says preordered because the fields are a preorder; there is no
      antisymmetry, and adding one would charge every operational law for
      a property no proof uses.
    - `IsCommGrade` — plus `join_comm`. Buys order-independence.
    - `IsIdemGrade` — plus `join_idem`. Buys length-independence.
    - `IsLubGrade` — plus `join_le`: `join` is a least upper bound, which
      is what makes a grade a semilattice rather than an ordered monoid.
    - `IsPartialOrderGrade` — plus `le_antisymm`: the order is a genuine
      partial order, so two grades below each other are one grade.

    The word "pomonoid" survives in lower case across this codebase and
    in `scripts/laws-inventory.py` as the name of the *property family* a
    law can consume — associativity, unit, order, commutativity,
    idempotence, and now antisymmetry. That is a vocabulary word, not a
    claim that any structure here is a partially ordered monoid; the
    structure is `PreorderedGradeMonoid`, and it is a preorder. Renaming
    the family across twelve modules would be churn with no reader on the
    other end, so it is recorded here instead of done.

    `IsCanonicalGrade` is an `abbrev` for the conjunction of the first
    two, not a class: with parameterised mixins the conjunction *is* the
    bundle, with no duplicated fields and no second route to either half.

    **What the four mixins are for is that they separate.** Three grades
    are instantiated below, and no two of them agree:

    | grade | LUB | comm | idem | antisym |
    |---|---|---|---|---|
    | `Grade Err` = `Finset Err` under `∪` | yes | yes | yes | yes |
    | `Nat` under `+` | no | yes | no | yes |
    | `Pack Err` = `List Err` under `++` | yes | no | no | **no** |

    `Pack` is the pre-canonical `error_set`: the argument pack as written,
    before the alias delegates to its sorted, deduplicated carrier. It is
    the first grade in this model to fail antisymmetry, which is what
    makes `IsPartialOrderGrade` worth stating at all — a class every
    instance satisfies discriminates nothing, and until `Pack` every
    instance did.

    **What that separation settles, and it is the point of this module's
    revision.** `IsIdemGrade.of_lub_of_antisymm` proves that the
    least-upper-bound law plus antisymmetry gives idempotence.
    `IsLubGrade.of_idem` proves the converse direction from monotonicity.
    Neither is an `instance`, so no grade acquires a second route to a
    class it already has directly. And `Pack` shows the antisymmetry
    hypothesis in the first of those is load-bearing rather than
    decorative: `Pack` has `IsLubGrade`, so `join_self_equiv` puts
    `join a a` and `a` each below the other, and `pack_not_idem` shows
    that this does *not* close into an equality. Commutativity and
    idempotence are what the quotient buys; antisymmetry is what turns
    the equivalence into the equality. That closes
    `docs/design.md#grade-join-strength`.

    `error_set`'s own two extra axioms (commutative, idempotent) are
    logically independent of each other, and this module states them
    as **independent mixins** over `PreorderedGradeMonoid`, not a nested chain
    (`IsIdemGrade extends IsCommGrade`, as an earlier revision of
    this module had it). [obligation-layering] resolved the provisional
    judgement call this module used to carry: `IsIdemGrade` no longer
    presupposes `IsCommGrade`, because no theorem in this file that
    cites `join_idem` also cites `join_comm` — `foldG_le` and
    `foldG_cons_ne_nil` need `join_idem` alone, `joinAllG_perm` needs
    `join_comm` alone, and nothing needs both. Nesting was smuggling an
    unneeded hypothesis into `foldG_le`/`foldG_cons_ne_nil`'s stated
    obligation; decoupling sharpens it to exactly what each proof uses,
    per `docs/RULES.md`'s hypothesis discipline. [grade-join-strength]
    then reversed the *shape* of that decoupling, and only the shape:
    where [obligation-layering] made each mixin `extends
    PreorderedGradeMonoid` so instance search had a single route to the
    base, the mixins now take the base as a class **parameter**. That
    reverses a decided question, so it carries an amendment — see
    `docs/RULES.md#amendments` for the reason, which is that the
    parameterised form is the only one in which `Pack` can inhabit
    `IsLubGrade` and not `IsPartialOrderGrade` without a diamond. No
    theorem's hypothesis got stronger or weaker in the move; `foldG_le`
    and its neighbours now name the base instance explicitly instead of
    receiving it through a projection. See `docs/design.md#obligations`
    for the classification this rests on.

    **What is deliberately *not* copied from `Graded/Grade.lean`.** Grade's
    own `join_le` (`g ⊆ k → h ⊆ k → g ∪ h ⊆ k`, proved directly by
    `Finset.union_subset`) and its two one-sided cousins `le_join_left`/
    `le_join_right` are *not* primitive fields of `PreorderedGradeMonoid` here. `join_le`
    is a least-upper-bound fact — it holds for `Finset` union because union
    genuinely is a semilattice join relative to `⊆` — and it is **not**
    implied by "associative, unital, ordered, monotone": the `Nat`
    counter-instance below satisfies every other field and still refutes
    `join_le` (`1 ⊆ 1` in the `≤` sense twice over, but `1 + 1 ≰ 1`). Making
    `join_le` a required field would make `Nat` unable to instantiate even
    `PreorderedGradeMonoid`, which would foreclose the whole demonstration this step
    exists to run. It is stated instead as the mixin `IsLubGrade`, which
    `Grade Err` and `Pack Err` inhabit and `Nat` does not — the shape that
    lets the semilattice question be *asked* of a grade rather than
    assumed of every grade. `le_join_left`/`le_join_right`, by contrast, *are*
    derivable from the fields kept (`join_mono`, `join_bot`/`bot_join`,
    `bot_le`) and are restated below as theorems, not fields, so the
    vocabulary still lines up with `Graded/Grade.lean` for
    [oracle-export](../tmp/plan/step-oracle-export.md)'s grep.

    **The headline consequence.** `join_le` itself is *recoverable* — but
    only from `join_mono` **and** `join_idem` together
    (`join_mono (le_refl' c) hb : join a c` is not what's wanted; the
    correct combination is `join_mono ha hb : join a b ≤ join c c`, then
    `join_idem c` collapses the right side to `c`). That means
    `foldG_le` — which the step brief predicted would need "`PreorderedGradeMonoid`
    alone" — actually needs `IsIdemGrade` (idempotence, not
    commutativity: its proof cites `join_idem` alone, never `join_comm`),
    the same class `foldG_cons_ne_nil` needs, once the grade's `join_le`
    is no longer assumed as a primitive. At the concrete `Grade` instance
    this is invisible,
    because `Grade.join_le` has a direct, cheap proof from `Finset` that
    never goes through `Grade.join_idem` — the per-instance proof and the
    generic derivation take different routes to the same fact. The `Nat`
    instance is the witness that the generic route is the only one
    available in general: `foldG (1 : Nat) [(), (), ()] = 3 ≰ 1`, so
    `foldG_le` genuinely fails at a non-idempotent commutative pomonoid,
    not merely `foldG_cons_ne_nil`. -/

namespace Graded

/-- A **pre**ordered monoid — the graded-monad literature's "pomonoid",
    under its standard reading (Katsumata's parametric effect monads are
    graded by exactly this structure; an earlier revision of this class
    misread "po" as *partially* ordered, and the rename says in full what
    the abbreviation meant): associative `join` with a two-sided unit
    `bot`, a *preorder* `le` — `le_refl'` and `le_trans'`, and no
    antisymmetry field — with `bot` as global minimum, and `join`
    monotone in both arguments. Commutativity, idempotence and
    antisymmetry are *not* here and are not the literature's either; they
    are the mixins below, and the model cites them only where a grade is
    spelled, never in an operational law (`docs/design.md#obligations`). Field names match the corresponding named
    lemmas in `Graded/Grade.lean` exactly, so a later grep sees one
    vocabulary rather than two. Deliberately *not* including `Grade`'s
    `join_le`/`le_join_left`/`le_join_right`: see the module docstring for
    why `join_le` cannot be a primitive field here (it would foreclose the
    `Nat` instance below), and why the other two are restated as theorems
    instead. -/
class PreorderedGradeMonoid (G : Type u) where
  join : G → G → G
  bot  : G
  le   : G → G → Prop
  join_assoc : ∀ a b c, join (join a b) c = join a (join b c)
  bot_join   : ∀ a, join bot a = a
  join_bot   : ∀ a, join a bot = a
  le_refl'   : ∀ a, le a a
  le_trans'  : ∀ {a b c}, le a b → le b c → le a c
  bot_le     : ∀ a, le bot a
  join_mono  : ∀ {a b c d}, le a b → le c d → le (join a c) (join b d)

/-- `PreorderedGradeMonoid` plus commutativity of `join`. A `Prop` mixin
    **parameterised by** the base instance, not extending it: there is one
    `PreorderedGradeMonoid G` in play, supplied by the caller, and this
    class adds a proof about it and no data. Buys order-independence:
    `joinAllG_perm` below, which is what licenses the C++ claim
    `error_set<X,Y> ≡ error_set<Y,X>` at the concrete `Grade` instance.

    Both counter-instances below inhabit the base class without inhabiting
    this one, in different ways: `Nat` is commutative and not idempotent,
    and `Pack` (the pre-canonical `error_set` written as a list) is
    neither, because appending two lists in the other order gives a
    different list. See [grade-join-strength] for what that separation
    settles. -/
class IsCommGrade (G : Type u) [PreorderedGradeMonoid G] : Prop where
  join_comm : ∀ a b : G,
    PreorderedGradeMonoid.join a b = PreorderedGradeMonoid.join b a

/-- `PreorderedGradeMonoid` plus idempotence of `join`, as an independent
    `Prop` mixin over the same base instance. Neither `foldG_le` nor
    `foldG_cons_ne_nil` below ever cites `join_comm`, so neither is
    charged for it. Buys length-independence: `foldG_cons_ne_nil` (and,
    as the module docstring explains, `foldG_le` too, once `join_le` is
    not assumed as a primitive), which is what makes the C++ `traverse`
    signature writable at all.

    Idempotence is an *equality*, and that is the whole content of
    [grade-join-strength]: `IsLubGrade` below gets `join a a` and `a`
    below each other in the order, and `Pack` is the witness that this
    does not close to an equality without antisymmetry
    (`IsIdemGrade.of_lub_of_antisymm`). -/
class IsIdemGrade (G : Type u) [PreorderedGradeMonoid G] : Prop where
  join_idem : ∀ a : G, PreorderedGradeMonoid.join a a = a

/-- `PreorderedGradeMonoid` plus the *least-upper-bound* law: `join a b`
    is below anything both `a` and `b` are below. This is what makes a
    grade a join-semilattice rather than merely an ordered monoid, and
    [grade-obligations] deliberately kept it out of the base class so
    that `Nat` under `+` could still be an instance of that. It is stated
    here as its own mixin instead, which is the shape that lets a grade
    have it *without* having idempotence: `Pack` does.

    The two directions between this and `IsIdemGrade` are both proved
    below and neither is an instance: `IsLubGrade.of_idem` goes one way
    with `join_mono`, and `IsIdemGrade.of_lub_of_antisymm` goes back only
    with antisymmetry in hand. -/
class IsLubGrade (G : Type u) [PreorderedGradeMonoid G] : Prop where
  join_le : ∀ {a b c : G}, PreorderedGradeMonoid.le a c →
    PreorderedGradeMonoid.le b c →
    PreorderedGradeMonoid.le (PreorderedGradeMonoid.join a b) c

/-- `PreorderedGradeMonoid` plus antisymmetry: the field the base class
    does not have, and the reason its name says "preordered". A grade
    inhabiting this one has a genuine partial order, so two grades below
    each other are the same grade.

    Until [truth-in-labelling] there was no point stating this, because
    every grade in the model satisfied it and a class everything inhabits
    discriminates nothing. `Pack` is the instance that fails it: `[A, A]`
    and `[A]` allow exactly the same error kinds and are not the same
    list. That failure is what `error_set`'s canonicalization exists to
    repair, and it is what makes the equalities in `IsCommGrade` and
    `IsIdemGrade` genuine content rather than restatements of the
    order. -/
class IsPartialOrderGrade (G : Type u) [PreorderedGradeMonoid G] : Prop where
  le_antisymm : ∀ {a b : G}, PreorderedGradeMonoid.le a b →
    PreorderedGradeMonoid.le b a → a = b

namespace PreorderedGradeMonoid
variable {G : Type u} [PreorderedGradeMonoid G]

/-- Derived, not primitive: `a ≤ join a b` follows from `join_mono`,
    `join_bot`, and `bot_le` alone — no commutativity, no idempotence.
    Restated here (rather than left implicit) only so the vocabulary
    matches `Graded.Grade.le_join_left` for the grep in
    [oracle-export](../tmp/plan/step-oracle-export.md); neither this nor
    `le_join_right` is used by any theorem in this module. -/
theorem le_join_left (a b : G) : le a (join a b) := by
  have h := join_mono (a := a) (b := a) (c := bot) (d := b) (le_refl' a) (bot_le b)
  rwa [join_bot] at h

/-- Derived, symmetric to `le_join_left`. -/
theorem le_join_right (a b : G) : le b (join a b) := by
  have h := join_mono (a := bot) (b := a) (c := b) (d := b) (bot_le a) (le_refl' b)
  rwa [bot_join] at h

end PreorderedGradeMonoid

/-- Recovers `Grade.join_le`'s shape (`a ≤ c → b ≤ c → join a b ≤ c`)
    generically — but only at the idempotent layer. `join_mono ha hb`
    gives `join a b ≤ join c c`; `join_idem c` is what collapses the right
    side to `c`. At the concrete `Grade` instance this fact has a *cheaper*
    direct proof (`Finset.union_subset`, no idempotence needed at all) —
    see the module docstring for why the generic route and the per-instance
    route diverge. -/
theorem join_le {G : Type u} [PreorderedGradeMonoid G] [IsIdemGrade G] {a b c : G}
    (ha : PreorderedGradeMonoid.le a c) (hb : PreorderedGradeMonoid.le b c) :
    PreorderedGradeMonoid.le (PreorderedGradeMonoid.join a b) c := by
  have h := PreorderedGradeMonoid.join_mono ha hb
  rwa [IsIdemGrade.join_idem c] at h

/-- **Idempotence implies the least-upper-bound law**, given monotonicity:
    `join_le` above, repackaged as the mixin. A `theorem`, deliberately
    **not** an `instance` — `Grade Err` has `IsLubGrade` directly from
    `Grade.join_le`, and registering this would give instance search a
    second route to the same class for that grade, which is the diamond
    `#obligations` has been avoiding since [obligation-layering]. -/
theorem IsLubGrade.of_idem {G : Type u} [PreorderedGradeMonoid G] [IsIdemGrade G] :
    IsLubGrade G :=
  ⟨fun ha hb => Graded.join_le ha hb⟩

/-- **The least-upper-bound law implies idempotence — but only with
    antisymmetry.** `join_le (le_refl' a) (le_refl' a)` puts `join a a`
    below `a`; `le_join_left a a` puts `a` below `join a a`; and closing
    those two into an equality is precisely what antisymmetry does, and
    what a preorder cannot do.

    This is the theorem `docs/design.md#grade-join-strength` was waiting
    on, and it is `Pack` (below) that gives it teeth: `Pack` inhabits
    `IsLubGrade` and not `IsPartialOrderGrade`, and its `join a a` is
    genuinely not `a`, so the antisymmetry hypothesis here is not
    decoration that every grade happens to satisfy. A `theorem`, not an
    `instance`, for the same no-second-route reason as
    `IsLubGrade.of_idem`. -/
theorem IsIdemGrade.of_lub_of_antisymm {G : Type u} [PreorderedGradeMonoid G]
    [IsLubGrade G] [IsPartialOrderGrade G] : IsIdemGrade G :=
  ⟨fun a => IsPartialOrderGrade.le_antisymm
    (IsLubGrade.join_le (PreorderedGradeMonoid.le_refl' a)
      (PreorderedGradeMonoid.le_refl' a))
    (PreorderedGradeMonoid.le_join_left a a)⟩

/-- **What the least-upper-bound law gives on its own**: `join a a` and
    `a` are each below the other. Every grade with `IsLubGrade` has this,
    including grades with no antisymmetry, and it is the exact strength
    `IsIdemGrade` adds an equality to. `Pack` below witnesses that the
    strengthening is real: it satisfies this and refutes `join a a = a`. -/
theorem join_self_equiv {G : Type u} [PreorderedGradeMonoid G] [IsLubGrade G] (a : G) :
    PreorderedGradeMonoid.le (PreorderedGradeMonoid.join a a) a ∧
      PreorderedGradeMonoid.le a (PreorderedGradeMonoid.join a a) :=
  ⟨IsLubGrade.join_le (PreorderedGradeMonoid.le_refl' a)
     (PreorderedGradeMonoid.le_refl' a),
   PreorderedGradeMonoid.le_join_left a a⟩

-- ---------------------------------------------------------------------
-- `Finset Err` satisfies all four classes, citing `Graded.Grade`'s named
-- lemmas — never reproving them. Each instance is built directly off
-- `instPreorderedGradeMonoidGrade`, not off another instance of this file's own
-- classes, so there is exactly one route to `PreorderedGradeMonoid (Grade Err)` no
-- matter which of the four is asked for — no diamond.

variable {Err : Type u} [DecidableEq Err]

instance instPreorderedGradeMonoidGrade : PreorderedGradeMonoid (Grade Err) where
  join := Grade.join
  bot  := Grade.bot
  le   := (· ⊆ ·)
  join_assoc := Grade.join_assoc
  bot_join   := Grade.bot_join
  join_bot   := Grade.join_bot
  le_refl'   := Grade.le_refl'
  le_trans'  := Grade.le_trans'
  bot_le     := Grade.bot_le
  join_mono  := Grade.join_mono

instance instCommGradeGrade : IsCommGrade (Grade Err) where
  join_comm := Grade.join_comm

instance instIdemGradeGrade : IsIdemGrade (Grade Err) where
  join_idem := Grade.join_idem

/-- `Grade Err` has the least-upper-bound law *directly*, from
    `Grade.join_le` (`Finset.union_subset`), never through
    `IsLubGrade.of_idem`. That the two routes exist and disagree in cost
    is the module docstring's finding about `join_le`. -/
instance instLubGradeGrade : IsLubGrade (Grade Err) where
  join_le := Grade.join_le

/-- `Grade Err` has antisymmetry, from `Grade.le_antisymm`
    (`Finset.Subset.antisymm`). With `IsLubGrade` above this is a second,
    independent route to `join_idem` for this grade, via
    `IsIdemGrade.of_lub_of_antisymm` — which is exactly why that lift is a
    theorem and not an instance. -/
instance instPartialOrderGradeGrade : IsPartialOrderGrade (Grade Err) where
  le_antisymm := Grade.le_antisymm

-- `IsCanonicalGrade` used to sit here, bundling `join_comm` and
-- `join_idem` as one named class because that conjunction is what
-- `error_set` promises. Parameterised mixins made the bundle
-- unnecessary: `[IsCommGrade G] [IsIdemGrade G]` *is* the conjunction,
-- with no duplicated fields and no second route to either one, so the
-- class was deleted rather than kept as an alias. The C++ reading it
-- carried survives as an abbreviation.

/-- "This grade's type promises canonical exact spelling": reordering and
    repetition both wash out. Not a class — an abbreviation for asking for
    the two mixins together, so the C++-facing name from
    [obligation-layering] survives the deletion of `IsCanonicalGrade`
    without reintroducing its duplicated fields. `Grade Err` satisfies it;
    `Nat` fails idempotence; `Pack` fails both. -/
abbrev IsCanonicalGrade (G : Type u) [PreorderedGradeMonoid G] : Prop :=
  IsCommGrade G ∧ IsIdemGrade G

/-- `Grade Err` inhabits the bundle: `Finset` union is both commutative
    and idempotent, so `Grade Err`'s type genuinely does promise canonical
    exact spelling — the fact `#obligations`' C++ reading rests on. -/
theorem grade_isCanonical : IsCanonicalGrade (Grade Err) :=
  ⟨⟨Grade.join_comm⟩, ⟨Grade.join_idem⟩⟩

-- ---------------------------------------------------------------------
-- The grade algebra, generic over an abstract `PreorderedGradeMonoid`. `foldG` and
-- `joinAllG` are the grade-only siblings of `Graded.Traverse.foldGrade`
-- and `Graded.Tuple.joinAll` — same shape, restated over `[PreorderedGradeMonoid G]`
-- with no carrier (`Graded g α`) in sight.

section FoldG
variable {G : Type u} [PreorderedGradeMonoid G] {α : Type v}

/-- The shape-fold grade, generic: `g` joined into itself once per list
    element, `PreorderedGradeMonoid.bot` at the base. The grade-only sibling of
    `Graded.Traverse.foldGrade`. -/
def foldG (g : G) : List α → G
  | []      => PreorderedGradeMonoid.bot
  | _ :: xs => PreorderedGradeMonoid.join g (foldG g xs)

theorem foldG_nil (g : G) : foldG g ([] : List α) = PreorderedGradeMonoid.bot := rfl

theorem foldG_cons (g : G) (x : α) (xs : List α) :
    foldG g (x :: xs) = PreorderedGradeMonoid.join g (foldG g xs) := rfl

end FoldG

-- `foldG_le` and `foldG_cons_ne_nil` now take `[PreorderedGradeMonoid G]`
-- and `[IsIdemGrade G]` as two arguments, which under
-- [obligation-layering]'s `extends` mixins would have been the instance
-- diamond that section was written to avoid. Under parameterised `Prop`
-- mixins it is not one: `IsIdemGrade G` carries no `PreorderedGradeMonoid
-- G` of its own to disagree with the one in scope — it is *indexed* by
-- it, so there is exactly one such term by construction rather than by
-- discipline. The hypothesis is the same strength it was; only its
-- spelling changed. See `docs/RULES.md`'s amendment and
-- `docs/design.md#obligations`.
section FoldGIdem
variable {G : Type u} [PreorderedGradeMonoid G] [IsIdemGrade G] {α : Type v}

/-- **Needs `IsIdemGrade`, not bare `PreorderedGradeMonoid`** — a stronger
    requirement than the step brief predicted. See the module docstring:
    without a primitive `join_le`, boundedness only comes back via
    `join_mono` + `join_idem` (the generic `join_le` above), and the `Nat`
    instance below is a witness that `PreorderedGradeMonoid`/`IsCommGrade` alone are
    not enough — `foldG (1 : Nat) [(), (), ()] = 3` is not `≤ 1`. -/
theorem foldG_le (g : G) : ∀ (xs : List α), PreorderedGradeMonoid.le (foldG g xs) g
  | [] => by
      rw [foldG_nil]; exact PreorderedGradeMonoid.bot_le g
  | x :: xs => by
      rw [foldG_cons]
      exact join_le (PreorderedGradeMonoid.le_refl' g) (foldG_le g xs)

/-- **This is the theorem [grade-obligations] was about.** A nonempty
    list's fold equals `g` exactly, regardless of length — needs
    `IsIdemGrade`, and does not typecheck at the bare `PreorderedGradeMonoid` layer
    (no `PreorderedGradeMonoid`-only proof exists; the `Nat` instance below is the
    witness). The proof itself cites only `join_bot` (`PreorderedGradeMonoid`) and
    `join_idem` (`IsIdemGrade`) — never `join_comm` — which is exactly
    why [obligation-layering] decoupled `IsIdemGrade` from
    `IsCommGrade`: this theorem never needed the commutativity the old
    nested hierarchy silently required alongside it. -/
theorem foldG_cons_ne_nil (g : G) :
    ∀ (xs : List α), xs ≠ [] → foldG g xs = g
  | [], h => absurd rfl h
  | [_], _ => by
      rw [foldG_cons, foldG_nil]
      exact PreorderedGradeMonoid.join_bot g
  | x :: y :: ys, _ => by
      rw [foldG_cons, foldG_cons_ne_nil g (y :: ys) (List.cons_ne_nil y ys)]
      exact IsIdemGrade.join_idem g

end FoldGIdem

section JoinAllG
variable {G : Type u} [PreorderedGradeMonoid G]

/-- The static fold of a list of *distinct* grades, generic: the grade-only
    sibling of `Graded.Tuple.joinAll`. Takes no repeated element grade `g`
    at all, unlike `foldG`. -/
def joinAllG : List G → G := List.foldr PreorderedGradeMonoid.join PreorderedGradeMonoid.bot

theorem joinAllG_nil : joinAllG ([] : List G) = PreorderedGradeMonoid.bot := rfl

theorem joinAllG_cons (g : G) (gs : List G) :
    joinAllG (g :: gs) = PreorderedGradeMonoid.join g (joinAllG gs) := rfl

end JoinAllG

-- `joinAllG_perm` takes the base instance and `[IsCommGrade G]`, for the
-- same reason the `foldG` section above does: with parameterised mixins
-- the two arguments cannot disagree.
section JoinAllGComm
variable {G : Type u} [PreorderedGradeMonoid G] [IsCommGrade G]

open List in
/-- **Needs `IsCommGrade`, exactly as the step brief predicted** —
    confirms rather than corrects it, and matches `Graded.Tuple.joinAll_perm`
    proof shape exactly (`nil`/`cons`/`swap`/`trans` induction on the
    permutation witness), citing `PreorderedGradeMonoid.join_assoc` and
    `IsCommGrade.join_comm` by name rather than reaching for a
    `Std.Commutative`/`Std.Associative` instance, per `docs/RULES.md`'s
    hypothesis discipline. -/
theorem joinAllG_perm {gs gs' : List G} (h : gs ~ gs') :
    joinAllG gs = joinAllG gs' := by
  induction h with
  | nil => rfl
  | cons g _ ih => simp only [joinAllG_cons, ih]
  | swap g g' gs =>
      simp only [joinAllG_cons]
      rw [← PreorderedGradeMonoid.join_assoc, ← PreorderedGradeMonoid.join_assoc,
        IsCommGrade.join_comm g g']
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end JoinAllGComm

-- ---------------------------------------------------------------------
-- The counter-instance: the naturals under `+`, `0`, `≤`. A commutative
-- pomonoid — associative, unital, ordered, monotone, commutative — that is
-- **not** idempotent (`1 + 1 ≠ 1`), so it is given `IsCommGrade` and
-- deliberately *not* `IsIdemGrade`.

instance instPreorderedGradeMonoidNat : PreorderedGradeMonoid Nat where
  join := (· + ·)
  bot  := 0
  le   := (· ≤ ·)
  join_assoc := Nat.add_assoc
  bot_join   := Nat.zero_add
  join_bot   := Nat.add_zero
  le_refl'   := Nat.le_refl
  le_trans'  := Nat.le_trans
  bot_le     := Nat.zero_le
  join_mono  := fun {_ _ _ _} hac hbd => Nat.add_le_add hac hbd

instance instCommGradeNat : IsCommGrade Nat where
  join_comm := Nat.add_comm

/-- `Nat` is antisymmetric (`Nat.le_antisymm`), and that is the point of
    stating it: antisymmetry alone buys nothing here, because `Nat` has no
    `IsLubGrade` instance for `IsIdemGrade.of_lub_of_antisymm` to consume.
    Before `Pack` existed, both grades in the model inhabited this class,
    which is why [truth-in-labelling] deferred stating it at all. -/
instance instPartialOrderGradeNat : IsPartialOrderGrade Nat where
  le_antisymm := Nat.le_antisymm

-- No `IsLubGrade Nat` instance: `1 ≤ 1` twice over, and `1 + 1 = 2 ≰ 1`,
-- refuted below. This is the exclusion `#obligations` records as the
-- reason `join_le` is not a field of the base class.

-- No `IsIdemGrade Nat` instance: `1 + 1 = 2 ≠ 1`, checked below.

theorem nat_not_idem : ¬ ∀ a : Nat, a + a = a := by
  intro h
  have := h 1
  simp at this

-- ---------------------------------------------------------------------
-- Products. The grade algebra is closed under pairs, componentwise —
-- which is what makes `Graded.Comp`'s *product-graded* composite
-- ([compose-applicative]) a graded carrier over a single grade rather
-- than a special case needing two of everything. Stated here rather than
-- beside `Comp` because it is a fact about grades, not about carriers.

/-- The componentwise product of two grades. Every field is the two
    underlying fields side by side; nothing is chosen. -/
instance instPreorderedGradeMonoidProd (G : Type u) (H : Type u)
    [PreorderedGradeMonoid G] [PreorderedGradeMonoid H] :
    PreorderedGradeMonoid (G × H) where
  join a b := (PreorderedGradeMonoid.join a.1 b.1, PreorderedGradeMonoid.join a.2 b.2)
  bot := (PreorderedGradeMonoid.bot, PreorderedGradeMonoid.bot)
  le a b := PreorderedGradeMonoid.le a.1 b.1 ∧ PreorderedGradeMonoid.le a.2 b.2
  join_assoc a b c := by
    simp only [Prod.mk.injEq]
    exact ⟨PreorderedGradeMonoid.join_assoc _ _ _, PreorderedGradeMonoid.join_assoc _ _ _⟩
  bot_join a := by
    simp only [PreorderedGradeMonoid.bot_join]
  join_bot a := by
    simp only [PreorderedGradeMonoid.join_bot]
  le_refl' a := ⟨PreorderedGradeMonoid.le_refl' _, PreorderedGradeMonoid.le_refl' _⟩
  le_trans' h₁ h₂ :=
    ⟨PreorderedGradeMonoid.le_trans' h₁.1 h₂.1, PreorderedGradeMonoid.le_trans' h₁.2 h₂.2⟩
  bot_le a := ⟨PreorderedGradeMonoid.bot_le _, PreorderedGradeMonoid.bot_le _⟩
  join_mono h₁ h₂ :=
    ⟨PreorderedGradeMonoid.join_mono h₁.1 h₂.1, PreorderedGradeMonoid.join_mono h₁.2 h₂.2⟩

/-- The product of two least-upper-bound grades is one: the bound is
    taken componentwise, so nothing is lost. -/
instance instLubGradeProd (G : Type u) (H : Type u)
    [PreorderedGradeMonoid G] [PreorderedGradeMonoid H] [IsLubGrade G] [IsLubGrade H] :
    IsLubGrade (G × H) where
  join_le h₁ h₂ := ⟨IsLubGrade.join_le h₁.1 h₂.1, IsLubGrade.join_le h₁.2 h₂.2⟩

-- ---------------------------------------------------------------------
-- The second counter-instance: the pre-canonical pack. `error_set<Es...>`
-- as the programmer wrote it, before the public alias delegates to its
-- sorted, deduplicated detail carrier. This is the grade that separates
-- a preorder from a partial order, which no other grade in this model
-- does.

/-- The **pre-canonical pack**: a grade written as a raw list of error
    kinds, in source order, with repeats left in. This is
    `error_set<A, B, A>` as typed, before `docs/design.md#representation`'s
    canonicalization runs — the argument pack, not the alias.

    `Grade Err` is this type's poset quotient and `Canon Err`
    (`Graded/Canonical.lean`) is a chosen normal form for that quotient.
    Stating the pack as its own grade is what turns that sentence from a
    remark into a demonstration: everything canonicalization buys shows up
    here as a law the pack fails. -/
abbrev Pack (Err : Type u) := List Err

namespace Pack
variable {Err : Type u}

/-- Order on packs: `g ≤ h` when every kind written in `g` is written
    somewhere in `h`. Repetition and order are invisible to it, which is
    the whole point — the pack carries data the order cannot see, and that
    is exactly antisymmetry failing. -/
def le (g h : Pack Err) : Prop := ∀ e ∈ g, e ∈ h

end Pack

variable {Err : Type u}

/-- The pack is a preordered grade monoid: concatenation for `join`, the
    empty pack for `bot`, `Pack.le` for the order. Every field of the base
    class holds, so nothing about the pack is disqualified from being a
    grade at the operational layer. -/
instance instPreorderedGradeMonoidPack : PreorderedGradeMonoid (Pack Err) where
  join := (· ++ ·)
  bot  := ([] : List Err)
  le   := Pack.le
  join_assoc := List.append_assoc
  bot_join   := List.nil_append
  join_bot   := List.append_nil
  le_refl'   := fun _ _ h => h
  le_trans'  := fun hab hbc e he => hbc e (hab e he)
  bot_le     := fun _ e he => absurd he List.not_mem_nil
  join_mono  := fun hab hcd e he => by
    rcases List.mem_append.mp he with h | h
    · exact List.mem_append.mpr (Or.inl (hab e h))
    · exact List.mem_append.mpr (Or.inr (hcd e h))

/-- **The pack is a least-upper-bound grade.** Concatenation genuinely is
    the join for `Pack.le`: anything both packs are below contains every
    kind of both, hence every kind of their concatenation. This is what
    separates the pack from `Nat` — `Nat` fails this law — and it is what
    makes the pack the witness `IsIdemGrade.of_lub_of_antisymm` needed:
    a grade with `join_le` and *without* idempotence. -/
instance instLubGradePack : IsLubGrade (Pack Err) where
  join_le := fun hac hbc e he => by
    rcases List.mem_append.mp he with h | h
    · exact hac e h
    · exact hbc e h

-- No `IsPartialOrderGrade (Pack Err)` instance, no `IsCommGrade`, and no
-- `IsIdemGrade`: all three are refuted below at the concrete `E`. This is
-- the first grade in the model to fail antisymmetry, and before it there
-- was no reason to state that class at all.

-- ---------------------------------------------------------------------
-- The demonstration, executable. Put the `Grade` and `Nat` cases adjacent:
-- the traversal grade is length-independent for `Grade` and grows without
-- bound for `Nat`, because idempotence is exactly what separates the two.

/-- The C++ error type stand-in, per `docs/RULES.md`. -/
inductive E | parse | range | io
  deriving DecidableEq, Repr

-- `Grade`: idempotent, so the traversal grade does not grow with the
-- list.
#guard foldG ({E.parse} : Grade E) [(), (), ()] = {E.parse}

-- `Nat`: commutative, ordered, monotone — and *not* idempotent, so the
-- traversal grade grows with the list exactly as
-- `docs/design.md#cpp-counterpart` warns a non-`error_set` grade might.
#guard foldG (1 : Nat) [(), (), ()] = 3

/-- **The headline disproof, length-independence.** `foldG_cons_ne_nil` —
    the theorem that makes the C++ `traverse` signature typeable for
    `error_set` — is *false* at the `Nat` grade: witnessed by exactly the
    `#guard` above (`foldG 1 [(), (), ()] = 3 ≠ 1`). -/
example : ¬ ∀ (g : Nat) (xs : List Unit), xs ≠ [] → foldG g xs = g := by
  intro h
  have := h 1 [(), (), ()] (by decide)
  simp [foldG, PreorderedGradeMonoid.join, PreorderedGradeMonoid.bot] at this

/-- **The other disproof, boundedness.** `foldG_le` is *also* false at the
    `Nat` grade, and for the same witness — the module docstring's finding
    that `foldG_le` needs `IsIdemGrade`, not bare `PreorderedGradeMonoid`, made
    concrete: `3 ≤ 1` is false. -/
example : ¬ ∀ (g : Nat) (xs : List Unit), PreorderedGradeMonoid.le (foldG g xs) g := by
  intro h
  have := h 1 [(), (), ()]
  simp only [foldG, PreorderedGradeMonoid.join, PreorderedGradeMonoid.bot,
    PreorderedGradeMonoid.le] at this
  omega

/-- **Order-independence survives where length-independence fails.**
    `joinAllG_perm` needs only `IsCommGrade` — which `Nat` *does* have —
    so it holds here even though `foldG_cons_ne_nil` does not. The two
    axioms buy different things: this is the clearest place in the project
    to see the split. -/
example : joinAllG ([1, 2, 3] : List Nat) = joinAllG ([3, 1, 2] : List Nat) :=
  joinAllG_perm (by decide)

#guard joinAllG ([1, 2, 3] : List Nat) = 6
#guard joinAllG ([3, 1, 2] : List Nat) = 6

-- ---------------------------------------------------------------------
-- The pack, at the concrete `E`. Everything canonicalization is for,
-- stated as three laws the pre-canonical spelling fails.

-- `[parse, parse]` and `[parse]` allow exactly the same error kinds, and
-- are not the same pack. Order and repetition are data the pack carries
-- and the order cannot see.
#guard ([E.parse, E.parse] : Pack E) ≠ [E.parse]
#guard ([E.parse] ++ [E.parse] : Pack E) = [E.parse, E.parse]
#guard ([E.parse] ++ [E.range] : Pack E) ≠ [E.range] ++ [E.parse]

/-- **The headline: the pack refutes `le_antisymm`.** `[parse, parse]` and
    `[parse]` are each below the other and are different packs, so `le`
    here is a preorder and nothing more. This is the first grade in the
    model to refute `IsPartialOrderGrade`, and it is why that class is
    worth stating: before the pack, every grade satisfied it. -/
theorem pack_not_antisymm : ¬ IsPartialOrderGrade (Pack E) := by
  intro hyp
  have := hyp.le_antisymm (a := ([E.parse, E.parse] : Pack E)) (b := [E.parse])
    (by intro e he; simp at he; simp [he]) (by intro e he; simp at he; simp [he])
  simp at this

/-- **`join_idem` fails as an equality.** `[parse] ++ [parse]` is
    `[parse, parse]`, not `[parse]`. The pack has `IsLubGrade`, so by
    `join_self_equiv` its `join a a` and `a` *are* each below the other:
    what fails is closing that to an equality, which is exactly the step
    `IsIdemGrade.of_lub_of_antisymm` spends antisymmetry on. Together with
    `pack_not_antisymm` this is the demonstration that the antisymmetry
    hypothesis in that theorem is load-bearing, not decoration. -/
theorem pack_not_idem : ¬ IsIdemGrade (Pack E) := by
  intro hyp
  have := hyp.join_idem ([E.parse] : Pack E)
  simp [PreorderedGradeMonoid.join] at this

/-- **`join_comm` fails as an equality too**, for the same reason and
    with the same repair: `[parse] ++ [range]` and `[range] ++ [parse]`
    allow the same kinds and are different lists. `error_set<A,B>` and
    `error_set<B,A>` being one type is the quotient's doing, not the
    pack's. -/
theorem pack_not_comm : ¬ IsCommGrade (Pack E) := by
  intro hyp
  have := hyp.join_comm ([E.parse] : Pack E) [E.range]
  simp [PreorderedGradeMonoid.join] at this

/-- **What the pack does have**, from `IsLubGrade` alone: `join a a` and
    `a` each below the other. Read against `pack_not_idem`, this is the
    precise gap antisymmetry closes, and the answer to
    `docs/design.md#grade-join-strength`: the least-upper-bound law does
    not imply idempotence over a preorder. -/
example : PreorderedGradeMonoid.le
      (PreorderedGradeMonoid.join ([E.parse] : Pack E) [E.parse]) [E.parse] ∧
    PreorderedGradeMonoid.le ([E.parse] : Pack E)
      (PreorderedGradeMonoid.join ([E.parse] : Pack E) [E.parse]) :=
  join_self_equiv ([E.parse] : Pack E)

end Graded
