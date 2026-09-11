import Graded.Signature
import Mathlib.Data.Finset.Empty

/-! The carrier: a value, or one error whose kind belongs to the grade.
    Models `expected<T, error_set<Es...>>`; at grade ∅ that C++ type is
    bare `T`, a genuinely different type, so this module asks Lean the
    honest question and gets back an `Equiv`, not an identity
    (`emptyEquiv` below).

    **`Graded` is a specialization, not a definition.** The carrier that
    carries a payload is `ExpectedG`, indexed by an `ErrorSignature`;
    `Graded` is `ExpectedG (tagOnly Err)`, every kind's payload `PUnit`.
    That is a *definitional* identity — `abbrev`, not `Equiv` — which is
    why the theorems written against `Graded` before [payload-carrier]
    are still theorems, without a single transport.

    Keeping them compiling took two mechanisms, both below:

    - `Graded.ok`/`Graded.err` are `@[match_pattern]` definitions, so
      `| .err e he => …` still elaborates though the real constructor
      takes three arguments.
    - `Graded.rec'` is a `@[cases_eliminator, induction_eliminator]`
      two-case recursor, so `cases x with | ok a | err e he` binds `he`
      to the *membership proof*. Without it `cases` binds the payload
      there and auto-names the membership — loud at most sites, and
      silent at any site that never uses `he`. -/

namespace Graded
variable {Err : Type u} [DecidableEq Err]

/-- A value of type `α`, or one error: its kind `k`, the payload that
    kind carries, and evidence that `k` belongs to the grade `g`.

    The membership argument is a `Prop`, hence proof-irrelevant, and
    contributes nothing to equality — `toSum` forgets it and
    `toSum_inj` is why that is sound. -/
inductive ExpectedG (S : ErrorSignature) [DecidableEq S.Kind]
    (g : Grade S.Kind) (α : Type w)
  | ok  : α → ExpectedG S g α
  | err : (k : S.Kind) → S.Payload k → k ∈ g → ExpectedG S g α

/-- The tag-only carrier: the model as it stood before payloads existed,
    recovered as the `PUnit`-payload specialization.

    **`def`, deliberately, not `abbrev`.** The two are definitionally
    equal either way, so every legacy theorem transfers regardless. What
    the `def` buys is *elaboration*: dot-notation resolves against the
    head of the expected type, and under an `abbrev` Lean sees through to
    `ExpectedG` and picks its three-argument `err` — so `.err e he` in
    every legacy definition becomes a partial application and fails. With
    a `def` the head stays `Graded` and `.err` finds the two-argument
    smart constructor below. The cost is that instance search stops here
    too, which is why the two instances are forwarded explicitly.

    The smart constructors are declared `Graded.ok`/`Graded.err` *inside*
    `namespace Graded`, so their full names are `Graded.Graded.ok` and
    `Graded.Graded.err` — the names the original constructors had. Dot
    notation resolves in the namespace of the expected type's head, which
    is `Graded.Graded`; declaring them one level up leaves `.err` finding
    `ExpectedG.err` again, with the same partial-application failure the
    `def` was meant to prevent. -/
def Graded (g : Grade Err) (α : Type v) : Type (max u v) :=
  ExpectedG (tagOnly Err) g α

namespace ExpectedG
variable {S : ErrorSignature} [DecidableEq S.Kind] {gs : Grade S.Kind} {α : Type w}

/-- Forget the membership proof. The only *data* an `ExpectedG` carries
    is a success payload or a kind-tagged error payload, and equality can
    be decided on that. -/
def toSum : ExpectedG S gs α → α ⊕ (Σ k : S.Kind, S.Payload k)
  | .ok a => .inl a
  | .err k p _ => .inr ⟨k, p⟩

theorem toSum_inj : Function.Injective (toSum (S := S) (gs := gs) (α := α)) := by
  intro x y h
  cases x with
  | ok a => cases y with
    | ok b => simp only [toSum, Sum.inl.injEq] at h; subst h; rfl
    | err k p m => simp [toSum] at h
  | err k p m => cases y with
    | ok b => simp [toSum] at h
    | err k' p' m' =>
        simp only [toSum, Sum.inr.injEq, Sigma.mk.injEq] at h
        obtain ⟨hk, hp⟩ := h
        subst hk
        simp only [heq_eq_eq] at hp
        subst hp
        rfl

/-- Decidable equality, given it for the success payload and for **each**
    member of the error payload family. That last obligation is one a
    concrete signature owes and cannot have synthesised for it. Every
    `#guard` in this repository reduces through this instance. -/
instance instDecidableEq [DecidableEq α] [∀ k, DecidableEq (S.Payload k)] :
    DecidableEq (ExpectedG S gs α) :=
  fun _ _ => decidable_of_iff _ toSum_inj.eq_iff

/-- `Repr`, with the same per-kind obligation as `instDecidableEq`. -/
instance instRepr [Repr α] [Repr S.Kind] [∀ k, Repr (S.Payload k)] :
    Repr (ExpectedG S gs α) where
  reprPrec x _ := match x with
    | .ok a => "ok " ++ repr a
    | .err k p _ => "err " ++ repr k ++ " " ++ repr p

end ExpectedG

-- ---------------------------------------------------------------------
-- The tag-only surface: constructors and eliminator presenting `Graded`
-- exactly as it looked before payloads, so every theorem written against
-- it stays written against it.

variable {g g' g'' : Grade Err} {α β γ : Type v}

/-- `ok`, unchanged. -/
@[match_pattern] def Graded.ok (a : α) : Graded g α := ExpectedG.ok a

/-- `err` at the tag-only signature: supplies the unit payload, so the
    two-argument spelling every earlier step uses still means what it
    meant. `@[match_pattern]` is what lets it appear in a pattern. -/
@[match_pattern] def Graded.err (e : Err) (he : e ∈ g) : Graded g α :=
  ExpectedG.err e ⟨⟩ he

-- Constructor behaviour, restated. An `inductive` gives `simp` the
-- injectivity and disjointness of its constructors for free; a pair of
-- `def`s does not, and `simp` cannot see through them to `ExpectedG`'s.
-- These four lemmas put back exactly what was free before, and they are
-- part of the surface the specialization owes: without them, proofs that
-- discharged `err ≠ ok` with a bare `simp` stop working, which is how
-- their absence was noticed.

@[simp] theorem Graded.ok_eq_ok {a b : α} :
    (Graded.ok a : Graded g α) = Graded.ok b ↔ a = b :=
  ⟨fun h => by injection h, fun h => h ▸ rfl⟩

@[simp] theorem Graded.err_eq_err {e e' : Err} {he : e ∈ g} {he' : e' ∈ g} :
    (Graded.err e he : Graded g α) = Graded.err e' he' ↔ e = e' :=
  ⟨fun h => by injection h, fun h => by subst h; rfl⟩

@[simp] theorem Graded.ok_ne_err {a : α} {e : Err} {he : e ∈ g} :
    (Graded.ok a : Graded g α) ≠ Graded.err e he := fun h => nomatch h

@[simp] theorem Graded.err_ne_ok {a : α} {e : Err} {he : e ∈ g} :
    (Graded.err e he : Graded g α) ≠ Graded.ok a := fun h => nomatch h

/-- Decidable equality and `Repr`, forwarded from `ExpectedG`. Instance
    search does not see through the `def` above, so these two lines are
    what keep every existing `#guard` reducing. -/
instance instDecidableEq [DecidableEq α] : DecidableEq (Graded g α) :=
  inferInstanceAs (DecidableEq (ExpectedG (tagOnly Err) g α))

instance instRepr [Repr α] [Repr Err] : Repr (Graded g α) :=
  inferInstanceAs (Repr (ExpectedG (tagOnly Err) g α))

/-- The two-case eliminator: at the unit payload there is nothing to bind
    for it, so `cases`/`induction` present the legacy shape. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def Graded.rec' {motive : Graded g α → Sort w}
    (ok : ∀ a, motive (Graded.ok a))
    (err : ∀ (e : Err) (he : e ∈ g), motive (Graded.err e he)) : ∀ x, motive x
  | ExpectedG.ok a => ok a
  | ExpectedG.err e ⟨⟩ he => err e he


/-- Apply a function to the `ok` payload; an `err` passes through unchanged.
    Note that `g` does not change and does not appear in the type of `f`:
    `map` is oblivious to grading, by construction rather than by proof. -/
def map (f : α → β) : Graded g α → Graded g β
  | .ok a => .ok (f a)
  | .err e he => .err e he

theorem map_id (x : Graded g α) : map (@id α) x = x := by
  cases x with
  | ok a => rfl
  | err e he => rfl

theorem map_comp (f : α → β) (h : β → γ) (x : Graded g α) :
    map (h ∘ f) x = map h (map f x) := by
  cases x with
  | ok a => rfl
  | err e he => rfl

/-- At grade ∅ no error is admissible, so `Graded ∅ α` is *isomorphic* to
    `α` — never `err`, only `ok`. It is not the *same type* as `α`: the
    `err` constructor still exists, it is merely uninhabited (its
    membership proof `e ∈ (∅ : Grade Err)` has no witness). C++'s bare
    `T` at grade ∅ is a different type from `expected<T, error_set<>>` for
    the same reason, but asserts the identification by implicit
    conversion, without proof; here the identification is proved. -/
def emptyEquiv : Graded (Grade.bot : Grade Err) α ≃ α where
  toFun
    | .ok a => a
    | .err _ he => absurd he (Finset.notMem_empty _)
  invFun a := .ok a
  left_inv x := by
    cases x with
    | ok a => rfl
    | err e he => exact absurd he (Finset.notMem_empty _)
  right_inv _ := rfl

/-- Naturality of the ∅-collapse: mapping before or after `emptyEquiv`
    agrees. This is what "bare `T` is safe at grade ∅" means: every
    operation on the isomorphic representations lines up. -/
theorem map_emptyEquiv (f : α → β) (x : Graded (Grade.bot : Grade Err) α) :
    emptyEquiv (map f x) = f (emptyEquiv x) := by
  cases x with
  | ok a => rfl
  | err e he => exact absurd he (Finset.notMem_empty _)

/-- Reinterpret a carrier at an equal grade. Later steps state laws "modulo
    grade equalities" through this family. -/
def cast (h : g = g') (x : Graded g α) : Graded g' α := h ▸ x

theorem cast_rfl (x : Graded g α) : cast rfl x = x := rfl

theorem cast_cast (h : g = g') (h' : g' = g'') (x : Graded g α) :
    cast h' (cast h x) = cast (h.trans h') x := by
  subst h; subst h'; rfl

end Graded
