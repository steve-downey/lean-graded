import Graded.Grade
import Mathlib.Data.Finset.Empty

/-! The carrier: a value, or one error whose kind belongs to the grade.
    Models `expected<T, error_set<Es...>>`; at grade ∅ that C++ type is
    bare `T`, a genuinely different type, so this module asks Lean the
    honest question and gets back an `Equiv`, not an identity
    (`emptyEquiv` below). -/

namespace Graded
variable {Err : Type u} [DecidableEq Err]

/-- A value of type `α`, or one error `e` together with the evidence that
    `e`'s kind belongs to the grade `g`. -/
inductive Graded (g : Grade Err) (α : Type v)
  | ok  : α → Graded g α
  | err : (e : Err) → e ∈ g → Graded g α

variable {g g' g'' : Grade Err} {α β γ : Type v}

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

instance instDecidableEq [DecidableEq α] :
    DecidableEq (Graded g α)
  | .ok a, .ok b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun heq => h (by injection heq))
  | .ok _, .err _ _ => isFalse (fun h => nomatch h)
  | .err _ _, .ok _ => isFalse (fun h => nomatch h)
  | .err e _, .err e' _ =>
      -- The membership proof is a `Prop`, so it is proof-irrelevant:
      -- two `err`s are equal iff their error values are, regardless of
      -- which membership witness each carries.
      if h : e = e' then isTrue (by subst h; rfl)
      else isFalse (fun heq => h (by injection heq))

end Graded
