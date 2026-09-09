import Graded.Grade

/-! What a grade has to be, stated as an obligation rather than an
    observation. `docs/design.md#cpp-counterpart` ends: "Only `error_set` is
    intended as a grade for now; the design should not make it the only
    possible grade." Fourteen prior steps each recorded which pomonoid
    property a law consumed, but `Graded.Grade Err` is a concrete `abbrev`
    for `Finset Err`, so nothing ever forced a proof to live inside its
    recorded budget, and no second grade was ever tried.

    This module states the budget as four Lean classes: one operational,
    three independent mixins over it.

    - `Pomonoid`          — associative join, a two-sided unit, a partial
                            order with `bot` as its minimum, and
                            monotonicity of `join` in the order. This is
                            the textbook "partially ordered monoid": an
                            `OrderedAddCommMonoid` without commutativity,
                            restated multiplicatively. **This is the
                            operational obligation** — every monad,
                            applicative, traversal, subsumption and
                            morphism law in `Graded/` needs at most this,
                            per [obligation-layering]'s classification.
    - `IsCommPomonoid`     — `Pomonoid` plus `join_comm`, on its own.
    - `IsIdemPomonoid`     — `Pomonoid` plus `join_idem`, on its own (not
                            through `IsCommPomonoid`).
    - `IsCanonicalPomonoid` — `Pomonoid` plus *both* `join_comm` and
                            `join_idem`, direct fields, not inherited from
                            the two classes above. Named for what a
                            **type** promises (canonical, exact spelling
                            — reordering and repetition both wash out) —
                            not because any theorem in this file needs the
                            conjunction (none does), but because that is
                            what `Grade Err` actually is, and what
                            `error_set` promises in C++.

    `error_set`'s own two extra axioms (commutative, idempotent) are
    logically independent of each other, and this module now states them
    as **independent siblings** of `Pomonoid`, not a nested chain
    (`IsIdemPomonoid extends IsCommPomonoid`, as an earlier revision of
    this module had it). [obligation-layering] resolved the provisional
    judgement call this module used to carry: `IsIdemPomonoid` no longer
    presupposes `IsCommPomonoid`, because no theorem in this file that
    cites `join_idem` also cites `join_comm` — `foldG_le` and
    `foldG_cons_ne_nil` need `join_idem` alone, `joinAllG_perm` needs
    `join_comm` alone, and nothing needs both. Nesting was smuggling an
    unneeded hypothesis into `foldG_le`/`foldG_cons_ne_nil`'s stated
    obligation; decoupling sharpens it to exactly what each proof uses,
    per `docs/RULES.md`'s hypothesis discipline. A third class,
    `IsCanonicalPomonoid`, bundles both axioms together — not because any
    theorem here needs the conjunction, but because that conjunction is
    what a real grade like `Grade Err` (`Finset` union) actually has, and
    it is the C++-facing name for "this grade's type promises canonical
    exact spelling." See `docs/design.md#obligations` (revised
    2026-09-08) for the classification this rests on.

    **What is deliberately *not* copied from `Graded/Grade.lean`.** Grade's
    own `join_le` (`g ⊆ k → h ⊆ k → g ∪ h ⊆ k`, proved directly by
    `Finset.union_subset`) and its two one-sided cousins `le_join_left`/
    `le_join_right` are *not* primitive fields of `Pomonoid` here. `join_le`
    is a least-upper-bound fact — it holds for `Finset` union because union
    genuinely is a semilattice join relative to `⊆` — and it is **not**
    implied by "associative, unital, ordered, monotone": the `Nat`
    counter-instance below satisfies every other field and still refutes
    `join_le` (`1 ⊆ 1` in the `≤` sense twice over, but `1 + 1 ≰ 1`). Making
    `join_le` a required field would make `Nat` unable to instantiate even
    `Pomonoid`, which would foreclose the whole demonstration this step
    exists to run. `le_join_left`/`le_join_right`, by contrast, *are*
    derivable from the fields kept (`join_mono`, `join_bot`/`bot_join`,
    `bot_le`) and are restated below as theorems, not fields, so the
    vocabulary still lines up with `Graded/Grade.lean` for
    [oracle-export](../tmp/plan/step-oracle-export.md)'s grep.

    **The headline consequence.** `join_le` itself is *recoverable* — but
    only from `join_mono` **and** `join_idem` together
    (`join_mono (le_refl' c) hb : join a c` is not what's wanted; the
    correct combination is `join_mono ha hb : join a b ≤ join c c`, then
    `join_idem c` collapses the right side to `c`). That means
    `foldG_le` — which the step brief predicted would need "`Pomonoid`
    alone" — actually needs `IsIdemPomonoid` (idempotence, not
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

/-- A partially ordered monoid: associative `join` with a two-sided unit
    `bot`, a partial order `le` with `bot` as global minimum, and `join`
    monotone in both arguments. Field names match the corresponding named
    lemmas in `Graded/Grade.lean` exactly, so a later grep sees one
    vocabulary rather than two. Deliberately *not* including `Grade`'s
    `join_le`/`le_join_left`/`le_join_right`: see the module docstring for
    why `join_le` cannot be a primitive field here (it would foreclose the
    `Nat` instance below), and why the other two are restated as theorems
    instead. -/
class Pomonoid (G : Type u) where
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

/-- `Pomonoid` plus commutativity of `join`, on its own — a sibling of
    `IsIdemPomonoid`, not its ancestor. Buys order-independence:
    `joinAllG_perm` below, which is what licenses the C++ claim
    `error_set<X,Y> ≡ error_set<Y,X>` at the concrete `Grade` instance.
    The `Nat` counter-instance below inhabits this class without
    inhabiting `IsIdemPomonoid`, which is exactly the point: commutativity
    without idempotence is a real, populated case, not a hypothetical one
    foreclosed by the class hierarchy's own shape. -/
class IsCommPomonoid (G : Type u) extends Pomonoid G where
  join_comm : ∀ a b, join a b = join b a

/-- `Pomonoid` plus idempotence of `join`, on its own — **not** through
    `IsCommPomonoid`. [obligation-layering] resolved the question an
    earlier revision of this module left open (nest, or sit beside): sit
    beside. Neither `foldG_le` nor `foldG_cons_ne_nil` below ever cites
    `join_comm`, so requiring it would have been an unneeded hypothesis on
    both — the nesting used to smuggle it in silently. Buys
    length-independence: `foldG_cons_ne_nil` below (and, as the module
    docstring explains, `foldG_le` too, once `join_le` is no longer
    assumed as a primitive) — which is what makes the C++ `traverse`
    signature writable at all. A grade that is idempotent without being
    commutative is not ruled out by the mathematics, and this class no
    longer rules it out either. -/
class IsIdemPomonoid (G : Type u) extends Pomonoid G where
  join_idem : ∀ a, join a a = a

/-- `Pomonoid` plus *both* `join_comm` and `join_idem`, stated as this
    class's own direct fields rather than by extending
    `IsCommPomonoid`/`IsIdemPomonoid` (avoiding the diamond back to
    `Pomonoid` that extending both would create). No theorem in this file
    takes `IsCanonicalPomonoid` as a hypothesis — every one that needs a
    pomonoid property needs exactly one of `join_comm`/`join_idem`, never
    their conjunction. This class exists to *name* the bundle a real grade
    inhabits: `Grade Err` gets an instance below (`Finset` union is both
    commutative and idempotent), `Nat` does not (it has `IsCommPomonoid`
    but is not idempotent). The C++ reading: a grade's *type* promises
    canonical exact spelling exactly when it inhabits this class, and
    [obligation-layering]'s classification is that no operational law
    needs that promise — only the grade's own bookkeeping
    (`foldG`/`foldGrade`) does. -/
class IsCanonicalPomonoid (G : Type u) extends Pomonoid G where
  join_comm : ∀ a b, join a b = join b a
  join_idem : ∀ a, join a a = a

namespace Pomonoid
variable {G : Type u} [Pomonoid G]

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

end Pomonoid

/-- Recovers `Grade.join_le`'s shape (`a ≤ c → b ≤ c → join a b ≤ c`)
    generically — but only at the idempotent layer. `join_mono ha hb`
    gives `join a b ≤ join c c`; `join_idem c` is what collapses the right
    side to `c`. At the concrete `Grade` instance this fact has a *cheaper*
    direct proof (`Finset.union_subset`, no idempotence needed at all) —
    see the module docstring for why the generic route and the per-instance
    route diverge. -/
theorem join_le {G : Type u} [IsIdemPomonoid G] {a b c : G}
    (ha : Pomonoid.le a c) (hb : Pomonoid.le b c) : Pomonoid.le (Pomonoid.join a b) c := by
  have h := Pomonoid.join_mono ha hb
  rwa [IsIdemPomonoid.join_idem c] at h

-- ---------------------------------------------------------------------
-- `Finset Err` satisfies all four classes, citing `Graded.Grade`'s named
-- lemmas — never reproving them. Each instance is built directly off
-- `instPomonoidGrade`, not off another instance of this file's own
-- classes, so there is exactly one route to `Pomonoid (Grade Err)` no
-- matter which of the four is asked for — no diamond.

variable {Err : Type u} [DecidableEq Err]

instance instPomonoidGrade : Pomonoid (Grade Err) where
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

instance instCommPomonoidGrade : IsCommPomonoid (Grade Err) where
  toPomonoid := instPomonoidGrade
  join_comm  := Grade.join_comm

instance instIdemPomonoidGrade : IsIdemPomonoid (Grade Err) where
  toPomonoid := instPomonoidGrade
  join_idem  := Grade.join_idem

/-- `Grade Err` inhabits the bundle: `Finset` union is both commutative
    and idempotent, so `Grade Err`'s type genuinely does promise canonical
    exact spelling — the fact `#obligations`' C++ reading rests on. -/
instance instCanonicalPomonoidGrade : IsCanonicalPomonoid (Grade Err) where
  toPomonoid := instPomonoidGrade
  join_comm  := Grade.join_comm
  join_idem  := Grade.join_idem

-- ---------------------------------------------------------------------
-- The grade algebra, generic over an abstract `Pomonoid`. `foldG` and
-- `joinAllG` are the grade-only siblings of `Graded.Traverse.foldGrade`
-- and `Graded.Tuple.joinAll` — same shape, restated over `[Pomonoid G]`
-- with no carrier (`Graded g α`) in sight.

section FoldG
variable {G : Type u} [Pomonoid G] {α : Type v}

/-- The shape-fold grade, generic: `g` joined into itself once per list
    element, `Pomonoid.bot` at the base. The grade-only sibling of
    `Graded.Traverse.foldGrade`. -/
def foldG (g : G) : List α → G
  | []      => Pomonoid.bot
  | _ :: xs => Pomonoid.join g (foldG g xs)

theorem foldG_nil (g : G) : foldG g ([] : List α) = Pomonoid.bot := rfl

theorem foldG_cons (g : G) (x : α) (xs : List α) :
    foldG g (x :: xs) = Pomonoid.join g (foldG g xs) := rfl

end FoldG

-- `foldG_le` and `foldG_cons_ne_nil` take `[IsIdemPomonoid G]` *alone*
-- (not also a separate `[Pomonoid G]`) so that instance search only ever
-- has one route to `Pomonoid G` — through `IsIdemPomonoid.toPomonoid`,
-- now a single hop since [obligation-layering] made `IsIdemPomonoid`
-- extend `Pomonoid` directly — rather than two independent instance
-- arguments that happen to agree. Mixing a bare `[Pomonoid G]` section
-- variable with an explicit `[IsIdemPomonoid G]` here is exactly the
-- "instance diamond" `linter.overlappingInstances` warns about, and it is
-- not merely a lint: the two `Pomonoid G` values are then genuinely
-- different terms, and `foldG_le`/`foldG_cons_ne_nil` (proved against
-- one) fail to apply against a proof term built against the other.
section FoldGIdem
variable {G : Type u} [IsIdemPomonoid G] {α : Type v}

/-- **Needs `IsIdemPomonoid`, not bare `Pomonoid`** — a stronger
    requirement than the step brief predicted. See the module docstring:
    without a primitive `join_le`, boundedness only comes back via
    `join_mono` + `join_idem` (the generic `join_le` above), and the `Nat`
    instance below is a witness that `Pomonoid`/`IsCommPomonoid` alone are
    not enough — `foldG (1 : Nat) [(), (), ()] = 3` is not `≤ 1`. -/
theorem foldG_le (g : G) : ∀ (xs : List α), Pomonoid.le (foldG g xs) g
  | [] => by
      rw [foldG_nil]; exact Pomonoid.bot_le g
  | x :: xs => by
      rw [foldG_cons]
      exact join_le (Pomonoid.le_refl' g) (foldG_le g xs)

/-- **This is the theorem [grade-obligations] was about.** A nonempty
    list's fold equals `g` exactly, regardless of length — needs
    `IsIdemPomonoid`, and does not typecheck at the bare `Pomonoid` layer
    (no `Pomonoid`-only proof exists; the `Nat` instance below is the
    witness). The proof itself cites only `join_bot` (`Pomonoid`) and
    `join_idem` (`IsIdemPomonoid`) — never `join_comm` — which is exactly
    why [obligation-layering] decoupled `IsIdemPomonoid` from
    `IsCommPomonoid`: this theorem never needed the commutativity the old
    nested hierarchy silently required alongside it. -/
theorem foldG_cons_ne_nil (g : G) :
    ∀ (xs : List α), xs ≠ [] → foldG g xs = g
  | [], h => absurd rfl h
  | [_], _ => by
      rw [foldG_cons, foldG_nil]
      exact Pomonoid.join_bot g
  | x :: y :: ys, _ => by
      rw [foldG_cons, foldG_cons_ne_nil g (y :: ys) (List.cons_ne_nil y ys)]
      exact IsIdemPomonoid.join_idem g

end FoldGIdem

section JoinAllG
variable {G : Type u} [Pomonoid G]

/-- The static fold of a list of *distinct* grades, generic: the grade-only
    sibling of `Graded.Tuple.joinAll`. Takes no repeated element grade `g`
    at all, unlike `foldG`. -/
def joinAllG : List G → G := List.foldr Pomonoid.join Pomonoid.bot

theorem joinAllG_nil : joinAllG ([] : List G) = Pomonoid.bot := rfl

theorem joinAllG_cons (g : G) (gs : List G) :
    joinAllG (g :: gs) = Pomonoid.join g (joinAllG gs) := rfl

end JoinAllG

-- `joinAllG_perm` takes `[IsCommPomonoid G]` alone, for the same
-- instance-diamond reason `foldG_le`/`foldG_cons_ne_nil` above take
-- `[IsIdemPomonoid G]` alone rather than sharing a section with a bare
-- `[Pomonoid G]` variable.
section JoinAllGComm
variable {G : Type u} [IsCommPomonoid G]

open List in
/-- **Needs `IsCommPomonoid`, exactly as the step brief predicted** —
    confirms rather than corrects it, and matches `Graded.Tuple.joinAll_perm`
    proof shape exactly (`nil`/`cons`/`swap`/`trans` induction on the
    permutation witness), citing `Pomonoid.join_assoc` and
    `IsCommPomonoid.join_comm` by name rather than reaching for a
    `Std.Commutative`/`Std.Associative` instance, per `docs/RULES.md`'s
    hypothesis discipline. -/
theorem joinAllG_perm {gs gs' : List G} (h : gs ~ gs') :
    joinAllG gs = joinAllG gs' := by
  induction h with
  | nil => rfl
  | cons g _ ih => simp only [joinAllG_cons, ih]
  | swap g g' gs =>
      simp only [joinAllG_cons]
      rw [← Pomonoid.join_assoc, ← Pomonoid.join_assoc, IsCommPomonoid.join_comm g g']
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end JoinAllGComm

-- ---------------------------------------------------------------------
-- The counter-instance: the naturals under `+`, `0`, `≤`. A commutative
-- pomonoid — associative, unital, ordered, monotone, commutative — that is
-- **not** idempotent (`1 + 1 ≠ 1`), so it is given `IsCommPomonoid` and
-- deliberately *not* `IsIdemPomonoid`.

instance instPomonoidNat : Pomonoid Nat where
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

instance instCommPomonoidNat : IsCommPomonoid Nat where
  toPomonoid := instPomonoidNat
  join_comm  := Nat.add_comm

-- No `IsIdemPomonoid Nat` instance: `1 + 1 = 2 ≠ 1`, checked below.

theorem nat_not_idem : ¬ ∀ a : Nat, a + a = a := by
  intro h
  have := h 1
  simp at this

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
  simp [foldG, Pomonoid.join, Pomonoid.bot] at this

/-- **The other disproof, boundedness.** `foldG_le` is *also* false at the
    `Nat` grade, and for the same witness — the module docstring's finding
    that `foldG_le` needs `IsIdemPomonoid`, not bare `Pomonoid`, made
    concrete: `3 ≤ 1` is false. -/
example : ¬ ∀ (g : Nat) (xs : List Unit), Pomonoid.le (foldG g xs) g := by
  intro h
  have := h 1 [(), (), ()]
  simp only [foldG, Pomonoid.join, Pomonoid.bot, Pomonoid.le] at this
  omega

/-- **Order-independence survives where length-independence fails.**
    `joinAllG_perm` needs only `IsCommPomonoid` — which `Nat` *does* have —
    so it holds here even though `foldG_cons_ne_nil` does not. The two
    axioms buy different things: this is the clearest place in the project
    to see the split. -/
example : joinAllG ([1, 2, 3] : List Nat) = joinAllG ([3, 1, 2] : List Nat) :=
  joinAllG_perm (by decide)

#guard joinAllG ([1, 2, 3] : List Nat) = 6
#guard joinAllG ([3, 1, 2] : List Nat) = 6

end Graded
