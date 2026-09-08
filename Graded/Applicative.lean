import Graded.Monad

/-! The applicative, derived from `bind`/`pure` rather than given its own
    primitive definition — checking the C++ claim
    (`docs/design.md#cpp-counterpart`) that the applicative instance for a
    monad *is* the monad instance. `ap` sequences its two arguments through
    `bind` in a fixed order — the function first, then the argument — so
    its result grade is `Grade.join g h` with the function's grade `g` on
    the left; `apFlipped` sequences the other way and lands at
    `Grade.join h g` instead.

    The four applicative laws below (`ap_pure_id`, `ap_comp`,
    `ap_pure_pure`, `ap_interchange`) need only the pomonoid's unit and
    associativity — never `join_comm`. `join_comm` shows up exactly once,
    in `ap_flip`: comparing `ap`'s grade `Grade.join g h` against
    `apFlipped`'s grade `Grade.join h g` is comparing a union's two
    arguments in the other order, which is what commutativity is. -/

namespace Graded
variable {Err : Type u} [DecidableEq Err]
variable {g g' h j : Grade Err} {α β γ : Type v}

/-- Sequence a graded function against a graded argument by threading both
    through `bind`/`pure`: apply `f`, then `x`. The inner grade `h ∪ ∅`
    collapses to `h` by `Grade.join_bot` — the one cast this definition
    needs. -/
def ap (f : Graded g (α → β)) (x : Graded h α) : Graded (Grade.join g h) β :=
  cast (congrArg (Grade.join g) (Grade.join_bot h))
    (bind f (fun f' => bind x (fun a => pure (f' a))))

/-- `ap`, sequenced the other way: the argument first, then the function.
    Lands at `Grade.join h g` — the same two grades, joined in the
    opposite order. -/
def apFlipped (f : Graded g (α → β)) (x : Graded h α) : Graded (Grade.join h g) β :=
  cast (congrArg (Grade.join h) (Grade.join_bot g))
    (bind x (fun a => bind f (fun f' => pure (f' a))))

/-- Combine two independently-graded computations with a binary function,
    via `ap` and `map`. -/
def map2 (k : α → β → γ) (x : Graded g α) (y : Graded h β) : Graded (Grade.join g h) γ :=
  ap (map k x) y

-- ---------------------------------------------------------------------
-- Reduction lemmas: how `ap` computes on each combination of constructors,
-- proved once so the laws below can `rw`/`simp` them instead of
-- re-deriving the `bind`/`cast` shuffle every time.

theorem ap_ok_ok (f' : α → β) (a : α) :
    ap (Graded.ok f' : Graded g (α → β)) (Graded.ok a : Graded h α) = Graded.ok (f' a) := by
  simp only [ap, bind, pure, widen]
  rw [cast_ok]

theorem ap_err_left (e : Err) (he : e ∈ g) (x : Graded h α) :
    ap (Graded.err e he : Graded g (α → β)) x = Graded.err e (Grade.le_join_left g h he) := by
  simp only [ap, bind]
  rw [cast_err]

theorem ap_ok_err (f' : α → β) (e : Err) (he : e ∈ h) :
    ap (Graded.ok f' : Graded g (α → β)) (Graded.err e he : Graded h α) =
      Graded.err e (Grade.le_join_right g h he) := by
  simp only [ap, bind, widen]
  rw [cast_err]

theorem apFlipped_ok_ok (f' : α → β) (a : α) :
    apFlipped (Graded.ok f' : Graded g (α → β)) (Graded.ok a : Graded h α) = Graded.ok (f' a) := by
  simp only [apFlipped, bind, pure, widen]
  rw [cast_ok]

theorem apFlipped_err_right (f : Graded g (α → β)) (e : Err) (he : e ∈ h) :
    apFlipped f (Graded.err e he : Graded h α) = Graded.err e (Grade.le_join_left h g he) := by
  simp only [apFlipped, bind]
  rw [cast_err]

theorem apFlipped_ok_err (a : α) (e : Err) (he : e ∈ g) :
    apFlipped (Graded.err e he : Graded g (α → β)) (Graded.ok a : Graded h α) =
      Graded.err e (Grade.le_join_right h g he) := by
  simp only [apFlipped, bind, widen]
  rw [cast_err]

-- ---------------------------------------------------------------------
-- The four applicative laws. Each cites the pomonoid property it needs,
-- per `docs/RULES.md`'s hypothesis discipline.

/-- (identity; unit) Applying `pure id` is the identity, up to
    `Grade.bot_join`. -/
theorem ap_pure_id (x : Graded h α) :
    cast (Grade.bot_join h) (ap (pure (@id α) : Graded Grade.bot (α → α)) x) = x := by
  cases x with
  | ok a => simp only [pure, ap_ok_ok, id]; rw [cast_ok]
  | err e he => simp only [pure, ap_ok_err]; rw [cast_err]

/-- (homomorphism; unit) Applying a `pure` function to a `pure` argument
    is the `pure` of the application, up to `Grade.bot_join` (equivalently
    `Grade.join_bot`, since both grades here are `∅`). -/
theorem ap_pure_pure (f : α → β) (a : α) :
    cast (Grade.bot_join Grade.bot)
        (ap (pure f : Graded (Grade.bot : Grade Err) (α → β)) (pure a)) =
      pure (f a) := by
  simp only [pure, ap_ok_ok]
  rw [cast_ok]

/-- (interchange) Applying `u` to a `pure` argument agrees with applying
    `pure (· a)` to `u`. Both sides collapse to the same grade `g` by the
    *unit* laws alone (`Grade.join_bot` on the left, `Grade.bot_join` on
    the right) — contrary to the naive expectation, this law does **not**
    need `Grade.join_comm`: `g ∪ ∅` and `∅ ∪ g` are each individually `g`,
    so nothing here ever compares them to each other. -/
theorem ap_interchange (u : Graded g (α → β)) (a : α) :
    cast (Grade.join_bot g) (ap u (pure a)) =
      cast (Grade.bot_join g) (ap (pure (fun f => f a)) u) := by
  cases u with
  | ok f' =>
    simp only [pure, ap_ok_ok]
    rw [cast_ok, cast_ok]
  | err e he =>
    simp only [pure, ap_err_left, ap_ok_err]
    rw [cast_err, cast_err]

/-- (composition; associative + unit) `ap` re-associates through `pure
    (· ∘ ·)` up to `Grade.bot_join` (dropping the leading `∅` that `pure`
    contributes) followed by `Grade.join_assoc` — no `Grade.join_comm`
    anywhere. -/
theorem ap_comp (u : Graded g (β → γ)) (v : Graded g' (α → β)) (w : Graded j α) :
    cast (by rw [Grade.bot_join, Grade.join_assoc] :
        Grade.join (Grade.join (Grade.join Grade.bot g) g') j = Grade.join g (Grade.join g' j))
        (ap (ap (ap (pure Function.comp :
            Graded (Grade.bot : Grade Err) ((β → γ) → (α → β) → α → γ)) u) v) w) =
      ap u (ap v w) := by
  cases u with
  | err e he =>
    simp only [pure, ap_ok_err, ap_err_left]
    rw [cast_err]
  | ok f' =>
    cases v with
    | err e he =>
      simp only [pure, ap_ok_ok, ap_ok_err, ap_err_left]
      rw [cast_err]
    | ok k =>
      cases w with
      | err e he =>
        simp only [pure, ap_ok_ok, ap_ok_err]
        rw [cast_err]
      | ok a =>
        simp only [pure, ap_ok_ok, Function.comp_apply]
        rw [cast_ok]

-- ---------------------------------------------------------------------
-- `ap_flip`: `ap` and `apFlipped` agree, but only when at most one side is
-- an error. This is the content of the C++ "the applicative instance is
-- identical to the monad instance" claim: identical *grade*, via
-- `Grade.join_comm`, and identical *value* only under a condition the C++
-- claim never states — see `Tests/Applicative.lean` for the
-- counterexample where both sides fail and the two disagree about which
-- error survives.

/-- `ap` and `apFlipped` agree as values whenever at most one of the two
    arguments is an error — i.e. at least one is `ok`. `Grade.join_comm`
    is needed here *by construction*: `ap`'s grade is `Grade.join g h`,
    `apFlipped`'s is `Grade.join h g`, the same union with its two
    arguments the other way around, and comparing them at all is exactly
    what commutativity says. This is the one and only place in this file
    that cites `Grade.join_comm`. -/
theorem ap_flip (f : Graded g (α → β)) (x : Graded h α)
    (honeok : (∃ f', f = Graded.ok f') ∨ (∃ a, x = Graded.ok a)) :
    ap f x = cast (Grade.join_comm h g) (apFlipped f x) := by
  rcases honeok with ⟨f', rfl⟩ | ⟨a, rfl⟩
  · cases x with
    | ok a => simp only [ap_ok_ok, apFlipped_ok_ok]; rw [cast_ok]
    | err e he => simp only [ap_ok_err, apFlipped_err_right]; rw [cast_err]
  · cases f with
    | ok f' => simp only [ap_ok_ok, apFlipped_ok_ok]; rw [cast_ok]
    | err e he => simp only [ap_err_left, apFlipped_ok_err]; rw [cast_err]

end Graded
