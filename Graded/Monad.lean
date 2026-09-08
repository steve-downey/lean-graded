import Graded.Widen

/-! The monad: `pure` puts a value in at grade `∅`; `bind` sequences two
    graded computations at their *union* grade. Models C++ `and_then`,
    whose result type is `expected<T, error_set<Es_f ∪ Es_g...>>` — a type
    computed by canonicalization, not a theorem. Here the union is a
    genuine `Finset` union, so the three monad laws only hold *up to* the
    pomonoid equalities from `Graded.Grade` (`bot_join`, `join_bot`,
    `join_assoc`), and are stated through `cast`.

    `bind` itself needs only the order half of the pomonoid: `widen` on
    the success path (via `Grade.le_join_right`) and `Grade.le_join_left`
    on the error path. Neither needs commutativity — the union's *left*
    argument is where the input's error lives, its *right* argument is
    where the continuation's error lives, and both sides are covered by
    the two one-sided inclusion lemmas rather than by `join_comm`. -/

namespace Graded
variable {Err : Type u} [DecidableEq Err]
variable {g g' h j : Grade Err} {α β γ : Type v}

/-- A value, at the empty grade: `pure` can never fail. -/
def pure (a : α) : Graded (Grade.bot : Grade Err) α := .ok a

/-- Sequence a graded computation into a continuation, at the *union* of
    the two grades. An `ok` hands its payload to `f` and widens the result
    from `h` up to `Grade.join g h` (`Grade.le_join_right`); an `err`
    carries its own membership proof along the other injection
    (`Grade.le_join_left`), without ever inspecting `f`. -/
def bind (x : Graded g α) (f : α → Graded h β) : Graded (Grade.join g h) β :=
  match x with
  | .ok a     => widen (Grade.le_join_right g h) (f a)
  | .err e he => .err e (Grade.le_join_left g h he)

-- Three small transport lemmas, generic in the grades involved, that do
-- the work every law below needs: pushing `cast` through the constructors
-- and through `widen`. Each is provable by `subst` on its equality
-- exactly as `Carrier.cast_cast` and `Widen.widen_cast` already are in
-- this codebase — no `grind` loop needed.

theorem cast_ok (e : g = g') (a : α) :
    cast e (Graded.ok a : Graded g α) = Graded.ok a := by
  subst e; rfl

theorem cast_err (e : g = g') (er : Err) (he : er ∈ g) :
    cast e (Graded.err er he : Graded g α) = Graded.err er (e ▸ he) := by
  subst e; rfl

/-- The mirror of `widen_cast`: casting after widening agrees with
    widening along the inclusion transported across the equality. -/
theorem cast_widen (h₁ : g ⊆ g') (e : g' = g'') (x : Graded g α) :
    cast e (widen h₁ x) = widen (e ▸ h₁) x := by
  subst e; rfl

/-- (unit) `pure` on the left of `bind` is the continuation itself, up to
    the grade equality `Grade.bot_join`. Cast is applied to the `bind`
    side — the compound `join` expression — using the pomonoid lemma in
    the direction it is already stated, so no `.symm` is needed here or
    at any use site. -/
theorem bind_pure_left (a : α) (f : α → Graded h β) :
    cast (Grade.bot_join h) (bind (pure a) f) = f a := by
  change cast (Grade.bot_join h) (widen (Grade.le_join_right Grade.bot h) (f a)) = f a
  rw [cast_widen]
  exact widen_refl (f a)

/-- (unit) `pure` on the right of `bind` is the original value, up to
    `Grade.join_bot`. -/
theorem bind_pure_right (x : Graded g α) :
    cast (Grade.join_bot g) (bind x (pure : α → Graded (Grade.bot : Grade Err) α)) = x := by
  cases x with
  | ok a =>
    change cast (Grade.join_bot g) (Graded.ok a : Graded (Grade.join g Grade.bot) α) =
      Graded.ok a
    exact cast_ok (Grade.join_bot g) a
  | err e he =>
    change cast (Grade.join_bot g) (Graded.err e (Grade.le_join_left g Grade.bot he)) =
      Graded.err e he
    rw [cast_err]

/-- (associative) `bind` re-associates up to `Grade.join_assoc`: the same
    fact C++ gets from `error_set`'s canonicalization, here a theorem
    about `Finset.union` transported through `cast`. -/
theorem bind_assoc (x : Graded g α) (f : α → Graded h β) (k : β → Graded j γ) :
    cast (Grade.join_assoc g h j) (bind (bind x f) k) =
      bind x (fun a => bind (f a) k) := by
  cases x with
  | ok a =>
    change cast (Grade.join_assoc g h j) (bind (widen (Grade.le_join_right g h) (f a)) k) =
      widen (Grade.le_join_right g (Grade.join h j)) (bind (f a) k)
    cases hfa : f a with
    | ok b =>
      change cast (Grade.join_assoc g h j)
          (widen (Grade.le_join_right (Grade.join g h) j) (k b)) =
        widen (Grade.le_join_right g (Grade.join h j))
          (widen (Grade.le_join_right h j) (k b))
      rw [cast_widen, widen_widen]
    | err e he =>
      change cast (Grade.join_assoc g h j)
          (Graded.err e (Grade.le_join_left (Grade.join g h) j ((Grade.le_join_right g h) he))) =
        Graded.err e ((Grade.le_join_right g (Grade.join h j)) (Grade.le_join_left h j he))
      rw [cast_err]
  | err e he =>
    change cast (Grade.join_assoc g h j)
        (Graded.err e (Grade.le_join_left (Grade.join g h) j (Grade.le_join_left g h he))) =
      Graded.err e (Grade.le_join_left g (Grade.join h j) he)
    rw [cast_err]

/-- (unit) `bind` with `pure ∘ f` is the same as `map f`, up to
    `Grade.join_bot` — the theorem saying the functor is the monad's
    functor. -/
theorem bind_map (f : α → β) (x : Graded g α) :
    cast (Grade.join_bot g) (bind x (pure ∘ f)) = map f x := by
  cases x with
  | ok a =>
    change cast (Grade.join_bot g) (Graded.ok (f a) : Graded (Grade.join g Grade.bot) β) =
      Graded.ok (f a)
    exact cast_ok (Grade.join_bot g) (f a)
  | err e he =>
    change cast (Grade.join_bot g) (Graded.err e (Grade.le_join_left g Grade.bot he)) =
      Graded.err e he
    rw [cast_err]

/-- (order) Subsumption commutes with `bind`: widening the input before
    binding agrees with binding then widening. The C++ side relies on
    this every time a narrower value flows into a wider continuation. -/
theorem bind_widen (h₁ : g ⊆ g') (x : Graded g α) (f : α → Graded h β) :
    bind (widen h₁ x) f = widen (Grade.join_mono h₁ (Grade.le_refl' h)) (bind x f) := by
  cases x with
  | ok a =>
    change widen (Grade.le_join_right g' h) (f a) =
      widen (Grade.join_mono h₁ (Grade.le_refl' h)) (widen (Grade.le_join_right g h) (f a))
    rw [widen_widen]
  | err e he => rfl

end Graded
