import Graded.Carrier

/-! Subsumption: the order half of the pomonoid, made computational. In C++
    a narrower `expected<T, error_set<Es...>>` converts implicitly to a
    wider one; `widen` is that conversion, and the theorems below are what
    make it a *functor* from the poset `(Grade, ⊆)` to endofunctors rather
    than an assumption: identity, composition, naturality, and agreement
    with every other way of changing a grade (`cast`, and the ∅-collapse
    from `Graded.Carrier`). -/

namespace Graded
variable {Err : Type u} [DecidableEq Err]
variable {g g' g'' : Grade Err} {α β : Type v}

/-- Reinterpret a carrier at a wider grade: `ok` is untouched, and an `err`
    carries its membership proof along `h`. Models the C++ implicit
    conversion `expected<T, error_set<Es...>> → expected<T,
    error_set<Es'...>>` for `Es ⊆ Es'`. -/
def widen (h : g ⊆ g') : Graded g α → Graded g' α
  | .ok a => .ok a
  | .err e he => .err e (h he)

/-- Widening along the reflexive inclusion (`Grade.le_refl'`) does nothing:
    the identity conversion is the identity. -/
theorem widen_refl (x : Graded g α) : widen (Grade.le_refl' g) x = x := by
  cases x with
  | ok a => rfl
  | err e he => rfl

/-- Widening twice, along `h₁ : g ⊆ g'` then `h₂ : g' ⊆ g''`, agrees with
    widening once along the composite inclusion (`Grade.le_trans'`): the
    conversion path doesn't matter, only its endpoints. -/
theorem widen_widen (h₁ : g ⊆ g') (h₂ : g' ⊆ g'') (x : Graded g α) :
    widen h₂ (widen h₁ x) = widen (Grade.le_trans' h₁ h₂) x := by
  cases x with
  | ok a => rfl
  | err e he => rfl

/-- Widening is natural in the payload: mapping before or after widening
    agrees. This is the "conversion commutes with everything else" half of
    functoriality. -/
theorem widen_map (h : g ⊆ g') (f : α → β) (x : Graded g α) :
    widen h (map f x) = map f (widen h x) := by
  cases x with
  | ok a => rfl
  | err e he => rfl

/-- Proof irrelevance: which proof of `g ⊆ g'` justifies the widening
    doesn't matter, only that one exists. `⊆` on a `Finset` is a `Prop`,
    so this is `Subsingleton.elim` under the hood — but stating it here is
    what turns "the conversion path doesn't matter" from a convention C++
    relies on into a theorem Lean checks. -/
theorem widen_irrel (h h' : g ⊆ g') (x : Graded g α) :
    widen h x = widen h' x := rfl

/-- Widening after a grade-equality `cast` agrees with widening along the
    inclusion transported across that equality: the two ways of changing a
    grade (proving `⊆` and proving `=`) commute. -/
theorem widen_cast (e : g = g') (h : g' ⊆ g'') (x : Graded g α) :
    widen h (cast e x) = widen (e ▸ h) x := by
  subst e; rfl

/-- The bare-`T` handoff: a plain value lifted directly into a carrier at
    any grade `g`, going through the ∅-collapse (`emptyEquiv`) and then
    widening along `Grade.bot_le`. This is the proved composite standing
    in for the C++ implicit conversion "a `T` is safe wherever a graded
    value is expected." -/
def fromEmpty (a : α) : Graded g α := widen (Grade.bot_le g) (emptyEquiv.symm a)

theorem fromEmpty_eq_ok (a : α) : (fromEmpty a : Graded g α) = .ok a := rfl

end Graded
