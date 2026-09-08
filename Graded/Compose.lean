import Graded.Traverse

/-! Composition: nested carriers, and the flattening that collapses them.
    In C++, `expected<expected<T, error_set<Es1...>>, error_set<Es2...>>`
    is routinely collapsed to `expected<T, error_set<Es1..., Es2...>>` —
    the union of the two error sets, computed by `error_set`'s own
    canonicalization and treated as obviously safe. It *is* safe, but the
    C++ code never states why: `flatten` below is that collapse, its
    natural grade is the *pair* `(g, h)` joined in the product pomonoid
    (not the union treated as one flat set — the two grades come from two
    genuinely different layers, and `join` is what identifies them), and
    it is exactly the monad's own multiplication (`flatten x = bind x
    id`), so its compatibility with `map`, `pure`, `bind` and `widen`
    inherits from [monad-laws] rather than needing fresh proofs. -/

namespace Graded
variable {Err : Type u} [DecidableEq Err]
variable {g g' h h' j : Grade Err} {α β γ : Type u}

/-- Collapse a nested carrier to a single one, at the joined grade. An
    `ok` of an `ok` is the payload; an `ok` of an `err` is that error,
    widened from the inner grade `h` up into `join g h`
    (`Grade.le_join_right`); an outer `err` is that error, widened from
    `g` into `join g h` (`Grade.le_join_left`). This is the monad
    multiplication: `flatten_eq_bind_id` below shows `flatten = bind ·
    id`, so every later law is really a `Graded.Monad` law in disguise. -/
def flatten : Graded g (Graded h α) → Graded (Grade.join g h) α
  | .ok (.ok a)      => .ok a
  | .ok (.err e he)  => .err e (Grade.le_join_right g h he)
  | .err e he        => .err e (Grade.le_join_left g h he)

/-- Exchange the two layers: an outer success wrapping an inner failure
    becomes an outer (now at the inner's former grade) failure, and an
    outer failure becomes an outer success wrapping an inner failure at
    the former outer grade. Used by `flatten_comm` below. -/
def swap : Graded g (Graded h α) → Graded h (Graded g α)
  | .ok (.ok a)      => .ok (.ok a)
  | .ok (.err e he)  => .err e he
  | .err e he        => .ok (.err e he)

/-- `flatten` *is* `bind` applied to the identity continuation — the
    carrier's monad multiplication, stated so that every compatibility
    law below can be read as a `Graded.Monad` law instantiated at `f :=
    id` rather than as a fresh fact about a second definition. -/
theorem flatten_eq_bind_id (x : Graded g (Graded h α)) :
    flatten x = bind x (fun y => y : Graded h α → Graded h α) := by
  cases x with
  | ok y =>
    cases y with
    | ok a => rfl
    | err e he => rfl
  | err e he => rfl

/-- Naturality in the payload: mapping the *inner* function `f` before
    flattening agrees with flattening then mapping `f` on the outside. -/
theorem flatten_map (f : α → β) (x : Graded g (Graded h α)) :
    flatten ((map (map f) x : Graded g (Graded h β))) = map f (flatten x) := by
  cases x with
  | ok y =>
    cases y with
    | ok a => rfl
    | err e he => rfl
  | err e he => rfl

/-- (unit) Wrapping an already-graded value with `pure` at the outer
    layer and flattening recovers the value itself, up to `Grade.bot_join`
    — the outer layer contributed no error, so it disappears entirely. -/
theorem flatten_pure_outer (y : Graded h α) :
    cast (Grade.bot_join h) (flatten (pure y)) = y := by
  cases y with
  | ok a =>
    change cast (Grade.bot_join h) (Graded.ok a : Graded (Grade.join Grade.bot h) α) =
      Graded.ok a
    exact cast_ok (Grade.bot_join h) a
  | err e he =>
    change cast (Grade.bot_join h)
        (Graded.err e (Grade.le_join_right Grade.bot h he)) =
      Graded.err e he
    rw [cast_err]

/-- (unit) Wrapping a graded value's payload with `pure` at the inner
    layer and flattening recovers the value itself, up to `Grade.join_bot`
    — the inner layer contributed no error. -/
theorem flatten_pure_inner (x : Graded g α) :
    cast (Grade.join_bot g) (flatten (map pure x)) = x := by
  cases x with
  | ok a =>
    change cast (Grade.join_bot g)
        (Graded.ok a : Graded (Grade.join g Grade.bot) α) = Graded.ok a
    exact cast_ok (Grade.join_bot g) a
  | err e he =>
    change cast (Grade.join_bot g)
        (Graded.err e (Grade.le_join_left g Grade.bot he)) =
      Graded.err e he
    rw [cast_err]

/-- (associative) Flattening twice — either the outer two layers first,
    then the result with the third, or the inner two layers first (via
    `map flatten`), then the result with the outer — agree up to
    `Grade.join_assoc`. This is the monad multiplication law: the same
    fact `bind_assoc` states for `bind`, here for three *nested carriers*
    rather than three sequenced computations. -/
theorem flatten_flatten (x : Graded g (Graded h (Graded j α))) :
    cast (Grade.join_assoc g h j) (flatten (flatten x)) = flatten (map flatten x) := by
  cases x with
  | ok y =>
    cases y with
    | ok z =>
      cases z with
      | ok a =>
        change cast (Grade.join_assoc g h j)
            (Graded.ok a : Graded (Grade.join (Grade.join g h) j) α) = Graded.ok a
        exact cast_ok (Grade.join_assoc g h j) a
      | err e he =>
        change cast (Grade.join_assoc g h j)
            (Graded.err e
              (Grade.le_join_right (Grade.join g h) j he)) =
          Graded.err e (Grade.le_join_right g (Grade.join h j) (Grade.le_join_right h j he))
        rw [cast_err]
    | err e he =>
      change cast (Grade.join_assoc g h j)
          (Graded.err e
            (Grade.le_join_left (Grade.join g h) j (Grade.le_join_right g h he))) =
        Graded.err e (Grade.le_join_right g (Grade.join h j) (Grade.le_join_left h j he))
      rw [cast_err]
  | err e he =>
    change cast (Grade.join_assoc g h j)
        (Graded.err e (Grade.le_join_left (Grade.join g h) j (Grade.le_join_left g h he))) =
      Graded.err e (Grade.le_join_left g (Grade.join h j) he)
    rw [cast_err]

/-- (order) Widening the outer layer before flattening agrees with
    flattening then widening the joined result along `Grade.join_mono`. -/
theorem flatten_widen_outer (h₁ : g ⊆ g') (x : Graded g (Graded h α)) :
    flatten (widen h₁ x) = widen (Grade.join_mono h₁ (Grade.le_refl' h)) (flatten x) := by
  cases x with
  | ok y =>
    cases y with
    | ok a => rfl
    | err e he => rfl
  | err e he => rfl

/-- (order) Widening the inner layer before flattening agrees with
    flattening then widening the joined result along `Grade.join_mono`. -/
theorem flatten_widen_inner (h₂ : h ⊆ h') (x : Graded g (Graded h α)) :
    flatten ((map (widen h₂) x : Graded g (Graded h' α))) =
      widen (Grade.join_mono (Grade.le_refl' g) h₂) (flatten x) := by
  cases x with
  | ok y =>
    cases y with
    | ok a => rfl
    | err e he => rfl
  | err e he => rfl

-- ---------------------------------------------------------------------
-- `flatten_comm`: unlike `ap_flip` (the first appearance of "at most one
-- side is an error") and `joinAll`'s accumulation (the second), this one
-- needs *no* hypothesis at all. `ap`/`apFlipped` combine two
-- *independent* graded values, each of which can independently be an
-- error, so which one's error survives the swap is a genuine question.
-- `flatten`'s nested carrier is not two independent values: it is a
-- single value, nested, so it holds at most one error already, by
-- construction — `Graded g (Graded h α)` has exactly three inhabited
-- shapes (`ok (ok _)`, `ok (err _ _)`, `err _ _`), never two errors at
-- once. The "at most one layer is an error" condition that mattered for
-- `ap_flip`/`joinAll` is *vacuously* true for every `flatten`/`swap`
-- input, so it need not be written down as a hypothesis here: this is
-- not a third confirmation of that condition, and not a different
-- condition either, but the case where the condition drops out entirely
-- because the shape it worried about cannot arise.

/-- Flattening agrees with flattening after swapping the two layers, up to
    `Grade.join_comm` — unconditionally. See the module comment above for
    why this needs no "at most one error" hypothesis, unlike `ap_flip`. -/
theorem flatten_comm (x : Graded g (Graded h α)) :
    flatten x = cast (Grade.join_comm h g) (flatten (swap x)) := by
  cases x with
  | ok y =>
    cases y with
    | ok a =>
      change (Graded.ok a : Graded (Grade.join g h) α) =
        cast (Grade.join_comm h g) (Graded.ok a : Graded (Grade.join h g) α)
      rw [cast_ok]
    | err e he =>
      change (Graded.err e (Grade.le_join_right g h he) : Graded (Grade.join g h) α) =
        cast (Grade.join_comm h g) (Graded.err e (Grade.le_join_left h g he))
      rw [cast_err]
  | err e he =>
    change (Graded.err e (Grade.le_join_left g h he) : Graded (Grade.join g h) α) =
      cast (Grade.join_comm h g) (Graded.err e (Grade.le_join_right h g he))
    rw [cast_err]

-- Traverse composition: attempted and found *false*, not merely
-- unproved — a concrete counterexample, and the exact statement, are
-- recorded in `tmp/plan/blocked-compose-flatten.md`. No theorem is
-- stated here for it: a disproved statement is not an admitted-with-a-
-- placeholder candidate.

end Graded
