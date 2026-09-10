import Graded.Applicative

/-! A second carrier, for the classic non-monad applicative: Validation,
    which combines independent checks and keeps *all* their errors. The
    plan's prediction was that this cannot share `Graded`'s carrier,
    because `Graded g α` holds exactly one error and an accumulating `ap`
    has nowhere to put the second. This module builds the alternative:
    `Accum g α` holds a *non-empty list* of in-grade errors, at the same
    grade `Graded` uses, connected back to it by `toGraded` (first
    error). `Accum` is not a fork of `Graded`: it is a different structure
    with a different law set, and it replaces `Graded` nowhere — every
    later step still uses `Graded`. -/

namespace Graded
variable {Err : Type u} [DecidableEq Err]

/-- A value, or a non-empty list of errors, each a member of the grade.
    Models a Validation-style `expected` that accumulates every failing
    check instead of stopping at the first.

    > **Provisional.** A `Multiset` is the mathematically right carrier for
    > an *unordered* bag of errors; a `List` with a non-emptiness proof is
    > the computable one actually used here. Picked for the same reason
    > `Graded.Carrier` picks `Finset` over an abstract order: something
    > that reduces under `#guard`/`decide` without extra tactics. Revisit
    > if a later consumer needs the errors as a genuinely unordered
    > collection (e.g. de-duplicating by grade membership alone). -/
inductive Accum (g : Grade Err) (α : Type v)
  | ok   : α → Accum g α
  | errs : (es : List Err) → es ≠ [] → (∀ e ∈ es, e ∈ g) → Accum g α

namespace Accum
variable {Err : Type u} [DecidableEq Err]
variable {g g' h j : Grade Err} {α β γ : Type v}

/-- A value, at the empty grade: `pure` can never fail, same as
    `Graded.pure`. -/
def pure (a : α) : Accum (Grade.bot : Grade Err) α := .ok a

/-- Apply a function to the `ok` payload; `errs` passes through unchanged
    (same list, same grade). -/
def map (f : α → β) : Accum g α → Accum g β
  | .ok a => .ok (f a)
  | .errs es hne hmem => .errs es hne hmem

/-- Subsumption for the accumulating carrier: every error keeps its
    place in the list and gains membership in the larger grade. The
    mirror of `Graded.widen` ([subsumption-widen]), and **it took until
    [abstract-effects] for anyone to notice it was missing** — no law in
    this module needed it, because `ap` builds its own membership proofs
    from `Grade.le_join_left`/`le_join_right` rather than by widening,
    and nothing else asked. The gap was invisible until the carrier was
    asked to be a graded functor in general, which is a use for the
    abstract layer independent of anything it proves. -/
def widen (h : g ⊆ h') : Accum g α → Accum h' α
  | .ok a => .ok a
  | .errs es hne hmem => .errs es hne (fun e he => h (hmem e he))

theorem widen_ok (h : g ⊆ h') (a : α) :
    (widen h (Accum.ok a) : Accum h' α) = Accum.ok a := rfl

theorem widen_errs (h : g ⊆ h') (es : List Err) (hne : es ≠ []) (hmem : ∀ e ∈ es, e ∈ g) :
    (widen h (Accum.errs es hne hmem) : Accum h' α)
      = Accum.errs es hne (fun e he => h (hmem e he)) := rfl

theorem widen_widen (h₁ : g ⊆ g') (h₂ : g' ⊆ h') (x : Accum g α) :
    widen h₂ (widen h₁ x) = widen (Grade.le_trans' h₁ h₂) x := by
  cases x <;> rfl

theorem widen_map (h : g ⊆ h') (f : α → β) (x : Accum g α) :
    widen h (map f x) = map f (widen h x) := by
  cases x <;> rfl

theorem map_id (x : Accum g α) : map id x = x := by
  cases x <;> rfl

theorem map_comp (f : α → β) (h : β → γ) (x : Accum g α) :
    map (h ∘ f) x = map h (map f x) := by
  cases x <;> rfl

/-- Sequence a graded function against a graded argument, *accumulating
    both* error lists when both sides fail — the one place this differs
    from `Graded.ap`, which can hold only one error and so must drop one
    side. The function's own errors come first in the concatenation,
    matching `ap`'s own argument order (`f` before `x`) and matching
    `Graded.ap`'s short-circuit priority when only one side fails
    (`ap_err_left`: the function's error always wins). Each membership
    proof is built from `Grade.le_join_left`/`le_join_right` alone,
    nothing more. -/
def ap (f : Accum g (α → β)) (x : Accum h α) : Accum (Grade.join g h) β :=
  match f, x with
  | .ok f', .ok a => .ok (f' a)
  | .ok _, .errs es hne hmem =>
      .errs es hne (fun e he => Grade.le_join_right g h (hmem e he))
  | .errs es hne hmem, .ok _ =>
      .errs es hne (fun e he => Grade.le_join_left g h (hmem e he))
  | .errs es1 hne1 hmem1, .errs es2 _hne2 hmem2 =>
      .errs (es1 ++ es2) (List.append_ne_nil_of_left_ne_nil hne1 es2)
        (fun e he => (List.mem_append.mp he).elim
          (fun h1 => Grade.le_join_left g h (hmem1 e h1))
          (fun h2 => Grade.le_join_right g h (hmem2 e h2)))

/-- Combine two independently-graded computations with a binary function,
    accumulating both error lists if both fail. -/
def map2 (k : α → β → γ) (x : Accum g α) (y : Accum h β) : Accum (Grade.join g h) γ :=
  ap (map k x) y

-- ---------------------------------------------------------------------
-- Reduction lemmas: how `ap` computes on each combination of
-- constructors. Each is `rfl` — `ap` is defined directly by pattern
-- match, with no `bind`/`cast` indirection to unfold — so the four/five
-- law proofs below can `cases` + `simp only` these instead of re-deriving
-- the match every time.

theorem ap_ok_ok (f' : α → β) (a : α) :
    ap (Accum.ok f' : Accum g (α → β)) (Accum.ok a : Accum h α) = Accum.ok (f' a) := rfl

theorem ap_ok_errs (f' : α → β) (es : List Err) (hne : es ≠ []) (hmem : ∀ e ∈ es, e ∈ h) :
    ap (Accum.ok f' : Accum g (α → β)) (Accum.errs es hne hmem : Accum h α) =
      Accum.errs es hne (fun e he => Grade.le_join_right g h (hmem e he)) := rfl

theorem ap_errs_ok (es : List Err) (hne : es ≠ []) (hmem : ∀ e ∈ es, e ∈ g) (a : α) :
    ap (Accum.errs es hne hmem : Accum g (α → β)) (Accum.ok a : Accum h α) =
      Accum.errs es hne (fun e he => Grade.le_join_left g h (hmem e he)) := rfl

theorem ap_errs_errs (es1 : List Err) (hne1 : es1 ≠ []) (hmem1 : ∀ e ∈ es1, e ∈ g)
    (es2 : List Err) (hne2 : es2 ≠ []) (hmem2 : ∀ e ∈ es2, e ∈ h) :
    ap (Accum.errs es1 hne1 hmem1 : Accum g (α → β)) (Accum.errs es2 hne2 hmem2 : Accum h α) =
      Accum.errs (es1 ++ es2) (List.append_ne_nil_of_left_ne_nil hne1 es2)
        (fun e he => (List.mem_append.mp he).elim
          (fun h1 => Grade.le_join_left g h (hmem1 e h1))
          (fun h2 => Grade.le_join_right g h (hmem2 e h2))) := rfl

/-- Reinterpret a carrier at an equal grade, mirroring `Graded.cast`. -/
def cast (e : g = g') (x : Accum g α) : Accum g' α := e ▸ x

theorem cast_ok (e : g = g') (a : α) :
    cast e (Accum.ok a : Accum g α) = Accum.ok a := by
  subst e; rfl

theorem cast_errs (e : g = g') (es : List Err) (hne : es ≠ []) (hmem : ∀ x ∈ es, x ∈ g) :
    cast e (Accum.errs es hne hmem : Accum g α) = Accum.errs es hne (e ▸ hmem) := by
  subst e; rfl

/-- Two `errs` values built from the same list, at the same grade, are
    equal regardless of which non-emptiness or membership proof each
    carries (both are `Prop`s, hence proof-irrelevant) — the `Accum`
    analogue of `Graded`'s `err`-case proof irrelevance
    (`Graded.instDecidableEq`). Used to close `ap_comp`'s all-`errs` case,
    where the two sides build the *same* list two different (but
    propositionally equal) ways. -/
theorem errs_eq_of_list_eq {es es' : List Err} {hne : es ≠ []} {hne' : es' ≠ []}
    {hmem : ∀ e ∈ es, e ∈ g} {hmem' : ∀ e ∈ es', e ∈ g} (heq : es = es') :
    (Accum.errs es hne hmem : Accum g α) = Accum.errs es' hne' hmem' := by
  subst heq; rfl

-- ---------------------------------------------------------------------
-- The four applicative laws. Each cites the pomonoid property it needs;
-- the all-`errs` leaf of `ap_comp` additionally cites `List.append_assoc`
-- — see the note there.

/-- (identity; unit) Applying `pure id` is the identity, up to
    `Grade.bot_join`. -/
theorem ap_pure_id (x : Accum h α) :
    cast (Grade.bot_join h) (ap (pure (@id α) : Accum Grade.bot (α → α)) x) = x := by
  cases x with
  | ok a => simp only [pure, ap_ok_ok, id]; rw [cast_ok]
  | errs es hne hmem => simp only [pure, ap_ok_errs]; rw [cast_errs]

/-- (homomorphism; unit) Applying a `pure` function to a `pure` argument
    is the `pure` of the application. -/
theorem ap_pure_pure (f : α → β) (a : α) :
    cast (Grade.bot_join Grade.bot)
        (ap (pure f : Accum (Grade.bot : Grade Err) (α → β)) (pure a)) =
      pure (f a) := by
  simp only [pure, ap_ok_ok]
  rw [cast_ok]

/-- (interchange) Applying `u` to a `pure` argument agrees with applying
    `pure (· a)` to `u`, up to the *unit* laws alone — no `Grade.join_comm`,
    same finding as [applicative-from-monad]'s `Graded.ap_interchange`. -/
theorem ap_interchange (u : Accum g (α → β)) (a : α) :
    cast (Grade.join_bot g) (ap u (pure a)) =
      cast (Grade.bot_join g) (ap (pure (fun f => f a)) u) := by
  cases u with
  | ok f' =>
    simp only [pure, ap_ok_ok]
    rw [cast_ok, cast_ok]
  | errs es hne hmem =>
    simp only [pure, ap_errs_ok, ap_ok_errs]
    rw [cast_errs, cast_errs]

/-- (composition; associative + unit) `ap` re-associates through `pure
    (· ∘ ·)`, up to `Grade.bot_join` and `Grade.join_assoc` on the grade —
    same as `Graded.ap_comp` — **and**, in the one leaf where `u`, `v`,
    and `w` all fail, `List.append_assoc` on the accumulated error list:
    the left side builds `(esu ++ esv) ++ esw`, the right side builds
    `esu ++ (esv ++ esw)`, the same list two different ways. This is new
    relative to `Graded.ap_comp`, which never has two simultaneous
    failures to concatenate. -/
theorem ap_comp (u : Accum g (β → γ)) (v : Accum g' (α → β)) (w : Accum j α) :
    cast (by rw [Grade.bot_join, Grade.join_assoc] :
        Grade.join (Grade.join (Grade.join Grade.bot g) g') j = Grade.join g (Grade.join g' j))
        (ap (ap (ap (pure Function.comp :
            Accum (Grade.bot : Grade Err) ((β → γ) → (α → β) → α → γ)) u) v) w) =
      ap u (ap v w) := by
  cases u with
  | ok f' =>
    cases v with
    | ok k =>
      cases w with
      | ok a =>
        simp only [pure, ap_ok_ok, Function.comp_apply]
        rw [cast_ok]
      | errs esw hnew hmemw =>
        simp only [pure, ap_ok_ok, ap_ok_errs]
        rw [cast_errs]
    | errs esv hnev hmemv =>
      cases w with
      | ok a =>
        simp only [pure, ap_ok_ok, ap_ok_errs, ap_errs_ok]
        rw [cast_errs]
      | errs esw hnew hmemw =>
        simp only [pure, ap_ok_ok, ap_ok_errs, ap_errs_errs]
        rw [cast_errs]
  | errs esu hneu hmemu =>
    cases v with
    | ok k =>
      cases w with
      | ok a =>
        simp only [pure, ap_ok_ok, ap_ok_errs, ap_errs_ok]
        rw [cast_errs]
      | errs esw hnew hmemw =>
        simp only [pure, ap_ok_errs, ap_errs_ok, ap_errs_errs]
        rw [cast_errs]
    | errs esv hnev hmemv =>
      cases w with
      | ok a =>
        simp only [pure, ap_ok_errs, ap_errs_errs, ap_errs_ok]
        rw [cast_errs]
      | errs esw hnew hmemw =>
        simp only [pure, ap_ok_errs, ap_errs_errs]
        rw [cast_errs]
        exact errs_eq_of_list_eq (List.append_assoc esu esv esw)

-- ---------------------------------------------------------------------
-- `Accum` is not a monad: no `bind` (of the shape `Graded.bind` has,
-- polymorphic in the grades and payload types) has a derived `ap` equal
-- to `Accum.ap`.
--
-- Witness: `f : Accum g (Unit → Empty)` fails. `f`'s payload type,
-- `Unit → Empty`, is *uninhabited* (a total function from an inhabited
-- type into `Empty` cannot exist), so the continuation any candidate
-- `bind f` would receive — `fun f' : Unit → Empty => bind x (fun a =>
-- pure (f' a))` — is a function *out of an uninhabited domain*. Any two
-- functions out of an uninhabited domain are equal (there is no point
-- where they could disagree), so this continuation is the *same term*
-- whether `x` is `.ok ()` or `.errs [e2] ..`: `bind f` cannot tell the
-- two apart, and so cannot produce different outputs for them. But
-- `Accum.ap f x` *does* tell them apart: it reports one error when `x`
-- succeeds and two when `x` also fails. No `bind` can match `ap` on both,
-- so no `bind`'s derived `ap` can equal `Accum.ap` at all.
--
-- This is the concrete form the step allows in place of a fully general
-- one: it is stated at one witnessing pair of grades (`{e1}`, `{e2}`)
-- rather than for all grades, but `bind` itself is left fully polymorphic
-- in the payload types and in the grades it is applied at — the same
-- shape `Graded.bind` has — so the obstruction is not an artifact of a
-- narrowed `bind` type.
theorem notMonad (e1 e2 : Err) :
    ¬ ∃ (bind : ∀ {g' h' : Grade Err} {α β : Type},
          Accum g' α → (α → Accum h' β) → Accum (Grade.join g' h') β),
      ∀ {g' h' : Grade Err} {α β : Type} (f : Accum g' (α → β)) (x : Accum h' α),
        cast (congrArg (Grade.join g') (Grade.join_bot h'))
            (bind f (fun f' => bind x (fun a => pure (f' a)))) = ap f x := by
  rintro ⟨bind, hbind⟩
  set f : Accum ({e1} : Grade Err) (Unit → Empty) :=
    Accum.errs [e1] (List.cons_ne_nil e1 []) (by simp) with hf
  set x1 : Accum ({e2} : Grade Err) Unit := Accum.ok () with hx1
  set x2 : Accum ({e2} : Grade Err) Unit :=
    Accum.errs [e2] (List.cons_ne_nil e2 []) (by simp) with hx2
  have hcont :
      (fun f' : Unit → Empty => bind x1 (fun a => pure (f' a))) =
      (fun f' : Unit → Empty => bind x2 (fun a => pure (f' a))) :=
    funext (fun f' => (f' ()).elim)
  have heq : ap f x1 = ap f x2 := by
    rw [← hbind f x1, ← hbind f x2, hcont]
  rw [hf, hx1, hx2, ap_errs_ok, ap_errs_errs] at heq
  have hlist : ([e1] : List Err) = [e1, e2] := by
    injection heq
  simp at hlist

-- ---------------------------------------------------------------------
-- The morphism back to `Graded`: take the first error. `Accum.sameGrade`
-- (`docs/design.md#applicative`) is not a Lean theorem but the two type
-- signatures side by side — both `ap`s are indexed by the same `Grade`
-- and the same `Grade.join`, only the carrier holding the error differs.

/-- Collapse to `Graded`'s one-error carrier: `ok` is untouched, `errs`
    keeps only its first error. -/
def toGraded : Accum g α → Graded g α
  | .ok a => .ok a
  | .errs [] hne _ => absurd rfl hne
  | .errs (e :: _) _ hmem => .err e (hmem e List.mem_cons_self)

theorem toGraded_ok (a : α) : (toGraded (Accum.ok a : Accum g α)) = Graded.ok a := rfl

theorem toGraded_errs (e : Err) (es : List Err) (hne : e :: es ≠ []) (hmem : ∀ x ∈ e :: es, x ∈ g) :
    toGraded (Accum.errs (e :: es) hne hmem : Accum g α) =
      Graded.err e (hmem e List.mem_cons_self) := rfl

/-- `toGraded` commutes with `ap`, **whenever at most one side fails** —
    the same condition [applicative-from-monad] found for `Graded.ap_flip`
    (`(∃ f', f = .ok f') ∨ (∃ a, x = .ok a)`): these are *the same
    condition*, discharged the same way
    (`rcases honeok with ⟨f', rfl⟩ | ⟨a, rfl⟩`).
    It in fact goes further than `ap_flip` needed to: because `Accum.ap`
    concatenates the function's errors *first* (`ap_errs_errs`), and
    `Graded.ap` always keeps the function's error when the function fails
    (`ap_err_left`, no condition at all), the *first* element of any
    accumulated list is always the function's own first error — so
    `toGraded` and `ap` in fact agree on **every** input, not just the
    one-sided ones. The hypothesis is recorded here, matching what
    `ap_flip` needed, but is not, in the end, load-bearing for this
    particular theorem; see `docs/design.md#applicative` for the
    unconditional statement (`toGraded_grade'`) this enabled. -/
theorem toGraded_grade (f : Accum g (α → β)) (x : Accum h α)
    (honeok : (∃ f', f = Accum.ok f') ∨ (∃ a, x = Accum.ok a)) :
    toGraded (ap f x) = Graded.ap (toGraded f) (toGraded x) := by
  rcases honeok with ⟨f', rfl⟩ | ⟨a, rfl⟩
  · cases x with
    | ok a => simp only [ap_ok_ok, toGraded_ok, Graded.ap_ok_ok]
    | errs es hne hmem =>
      cases es with
      | nil => exact absurd rfl hne
      | cons e es' =>
        simp only [ap_ok_errs, toGraded_errs, toGraded_ok, Graded.ap_ok_err]
  · cases f with
    | ok f' => simp only [ap_ok_ok, toGraded_ok, Graded.ap_ok_ok]
    | errs es hne hmem =>
      cases es with
      | nil => exact absurd rfl hne
      | cons e es' =>
        simp only [ap_errs_ok, toGraded_errs, Graded.ap_err_left]

/-- The unconditional form: `toGraded` commutes with `ap` on **every**
    input, including when both sides fail. This is *stronger* than the
    step predicted (`toGraded_grade` above states only the one-sided
    version the step asked for) — see `docs/design.md#applicative` for
    why: it is a consequence of two choices, each independently the
    natural one, lining up — `Accum.ap`'s concatenation puts the
    function's errors first, and `Graded.ap` always keeps the function's
    error when the function fails — so "first element of the accumulated
    list" and "the error `Graded.ap` keeps" are the same error by
    construction, not by coincidence. -/
theorem toGraded_grade' (f : Accum g (α → β)) (x : Accum h α) :
    toGraded (ap f x) = Graded.ap (toGraded f) (toGraded x) := by
  cases f with
  | ok f' =>
    cases x with
    | ok a => simp only [ap_ok_ok, toGraded_ok, Graded.ap_ok_ok]
    | errs es hne hmem =>
      cases es with
      | nil => exact absurd rfl hne
      | cons e es' =>
        simp only [ap_ok_errs, toGraded_errs, toGraded_ok, Graded.ap_ok_err]
  | errs esf hnef hmemf =>
    cases esf with
    | nil => exact absurd rfl hnef
    | cons e esf' =>
      cases x with
      | ok a =>
        simp only [ap_errs_ok, toGraded_errs, Graded.ap_err_left]
      | errs es hne hmem =>
        cases es with
        | nil => exact absurd rfl hne
        | cons e' es' =>
          simp only [ap_errs_errs, List.cons_append, toGraded_errs, Graded.ap_err_left]

end Accum
end Graded
