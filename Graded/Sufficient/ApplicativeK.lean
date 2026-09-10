import Graded.Sufficient.MonadK
import Graded.Applicative

/-! `apK`/`map2K`/`apFlippedK`: the applicative at a sufficient grade.

    Split out of the former single `Graded/Sufficient.lean` by
    [module-split]; `Graded.Sufficient` is now a re-export shim over the
    six pieces, so every existing import keeps working. -/

namespace Graded

variable {Err : Type u} [DecidableEq Err]
variable {g h j k : Grade Err} {α β γ : Type v}

-- ---------------------------------------------------------------------
-- `apK`/`map2K`: the applicative at a sufficient grade, built through
-- `bindK` exactly as `Graded.ap`/`Graded.map2` are built through `bind` —
-- the same "the applicative is the monad's" story, one layer up. Unlike
-- `ap`, which sequences through `bind`'s *computed* union and pays one
-- cast collapsing the inner `h ∪ ∅` back to `h`, `apK` never introduces a
-- `∅` in the first place: `pureK`'s target grade is `k` directly (the
-- same fact `pureK`'s own docstring already established — it *is* `pure`
-- widened to any grade, not `pure` itself), so both of `ap`'s two `bind`
-- calls land at `k` immediately, via `Grade.le_refl' k`, with nothing to
-- collapse.

/-- Combine a graded function and a graded argument at any grade `k`
    known to contain both — `ap`'s own two-step `bind`/`pure` shuffle,
    with `pureK` used in place of `pure` so the intermediate step already
    sits at `k` instead of at `Grade.bot`. The "third obligation" the step
    predicted (one hypothesis per input, plus one for `pure`'s own grade)
    does not merely come out free by proof irrelevance the way `bindK`'s
    two threaded proofs do — it never appears in this signature at all,
    because `pureK` needs no inclusion proof of its own to be a value at
    `k`. -/
def apK (hg : g ⊆ k) (hh : h ⊆ k) (f : Graded g (α → β)) (x : Graded h α) :
    Graded k β :=
  bindK hg (Grade.le_refl' k) f
    (fun f' => bindK hh (Grade.le_refl' k) x (fun a => pureK (f' a)))

/-- `map2` at a sufficient grade: `apK` after `map`, exactly as `map2` is
    `ap` after `map`. -/
def map2K (hg : g ⊆ k) (hh : h ⊆ k) (f : α → β → γ) (x : Graded g α) (y : Graded h β) :
    Graded k γ :=
  apK hg hh (map f x) y

-- Reduction lemmas: `apK`'s own ok/err shapes, the mirror of
-- `ap_ok_ok`/`ap_err_left`/`ap_ok_err`, all `rfl` for the same reason
-- `bindK_ok`/`bindK_err` already are — every hypothesis threaded through
-- is a `Prop`, so which one is supplied never affects the reduction.

theorem apK_ok_ok (hg : g ⊆ k) (hh : h ⊆ k) (f' : α → β) (a : α) :
    apK hg hh (Graded.ok f' : Graded g (α → β)) (Graded.ok a : Graded h α) =
      Graded.ok (f' a) := rfl

theorem apK_err_left (hg : g ⊆ k) (hh : h ⊆ k) (e : Err) (he : e ∈ g) (x : Graded h α) :
    apK hg hh (Graded.err e he : Graded g (α → β)) x = Graded.err e (hg he) := rfl

theorem apK_ok_err (hg : g ⊆ k) (hh : h ⊆ k) (f' : α → β) (e : Err) (he : e ∈ h) :
    apK hg hh (Graded.ok f' : Graded g (α → β)) (Graded.err e he : Graded h α) =
      Graded.err e (hh he) := rfl

-- ---------------------------------------------------------------------
-- `apFlippedK`: the other sequencing order, at the *same* sufficient
-- grade `k` — built so `apK_flip` below can ask its question at one
-- grade instead of two.

/-- `apK`, sequenced the other way: the argument first, then the
    function — the sufficient-grade mirror of `apFlipped`, landing at the
    same target grade `k` as `apK` rather than at a second, differently-
    joined grade. -/
def apFlippedK (hg : g ⊆ k) (hh : h ⊆ k) (f : Graded g (α → β)) (x : Graded h α) :
    Graded k β :=
  bindK hh (Grade.le_refl' k) x
    (fun a => bindK hg (Grade.le_refl' k) f (fun f' => pureK (f' a)))

theorem apFlippedK_ok_ok (hg : g ⊆ k) (hh : h ⊆ k) (f' : α → β) (a : α) :
    apFlippedK hg hh (Graded.ok f' : Graded g (α → β)) (Graded.ok a : Graded h α) =
      Graded.ok (f' a) := rfl

theorem apFlippedK_err_right (hg : g ⊆ k) (hh : h ⊆ k) (f : Graded g (α → β))
    (e : Err) (he : e ∈ h) :
    apFlippedK hg hh f (Graded.err e he : Graded h α) = Graded.err e (hh he) := rfl

theorem apFlippedK_ok_err (hg : g ⊆ k) (hh : h ⊆ k) (a : α) (e : Err) (he : e ∈ g) :
    apFlippedK hg hh (Graded.err e he : Graded g (α → β)) (Graded.ok a : Graded h α) =
      Graded.err e (hg he) := rfl

-- ---------------------------------------------------------------------
-- The four applicative laws, cast-free. Every one of them mentions only
-- `Grade.le_refl'` — the hypothesis that lets `pureK` land at `k`
-- directly — never a unit or associativity lemma: at a common sufficient
-- grade there is no `∅` anywhere in these statements for a unit law to
-- collapse, and no re-association of a `join` for an associativity law to
-- justify. The property these laws consume is the same "order" tag
-- `bindK`'s own three laws already carry, not a new one.

theorem apK_pure_id (hh : h ⊆ k) (x : Graded h α) :
    apK (Grade.le_refl' k) hh (pureK (@id α) : Graded k (α → α)) x = widen hh x := by
  cases x using Graded.rec' with
  | ok a => rfl
  | err e he => rfl

theorem apK_pure_pure (f : α → β) (a : α) :
    apK (Grade.le_refl' k) (Grade.le_refl' k) (pureK f : Graded k (α → β))
        (pureK a : Graded k α) =
      (pureK (f a) : Graded k β) := rfl

/-- (interchange) At a common sufficient grade `k` there is only one
    grade in sight, so unlike `ap_interchange` (which needs `Grade.join_bot`
    and `Grade.bot_join` separately, one per side) this needs no property
    beyond `pureK` landing directly at `k` on both sides. -/
theorem apK_interchange (hg : g ⊆ k) (u : Graded g (α → β)) (a : α) :
    apK hg (Grade.le_refl' k) u (pureK a : Graded k α) =
      apK (Grade.le_refl' k) hg (pureK (fun f => f a) : Graded k ((α → β) → β)) u := by
  cases u using Graded.rec' with
  | ok f' => rfl
  | err e he => rfl

theorem apK_comp (hg : g ⊆ k) (hg' : g' ⊆ k) (hj : j ⊆ k)
    (u : Graded g (β → γ)) (v : Graded g' (α → β)) (w : Graded j α) :
    apK (Grade.le_refl' k) hj
        (apK (Grade.le_refl' k) hg'
          (apK (Grade.le_refl' k) hg
            (pureK Function.comp : Graded k ((β → γ) → (α → β) → α → γ)) u) v) w =
      apK hg (Grade.le_refl' k) u (apK hg' hj v w) := by
  cases u using Graded.rec' with
  | err e he => rfl
  | ok uf =>
    cases v using Graded.rec' with
    | err e he => rfl
    | ok vf =>
      cases w using Graded.rec' with
      | err e he => rfl
      | ok wa => rfl

-- ---------------------------------------------------------------------
-- `apK_flip`: the finding this step exists to make. `ap_flip` needs
-- `Grade.join_comm` *by construction* — it compares `ap`'s grade
-- `Grade.join g h` against `apFlipped`'s `Grade.join h g`, two different
-- expressions for the same grade. At a common sufficient grade `k`,
-- `apK` and `apFlippedK` both already land in `Graded k β`: there is no
-- second expression for the same grade anywhere, so there is nothing for
-- `Grade.join_comm` to relate. This is the one place in this file
-- structurally shaped like the union-graded theorem that *does* need
-- commutativity, and it needs no property at all — commutativity, on this
-- evidence, was a cost of *computing* the grade exactly (so that the two
-- orderings had to be reconciled after the fact), not a requirement of
-- the applicative structure itself.

theorem apK_flip (hg : g ⊆ k) (hh : h ⊆ k) (f : Graded g (α → β)) (x : Graded h α)
    (honeok : (∃ f', f = Graded.ok f') ∨ (∃ a, x = Graded.ok a)) :
    apK hg hh f x = apFlippedK hg hh f x := by
  rcases honeok with ⟨f', rfl⟩ | ⟨a, rfl⟩
  · cases x with
    | ok a => rw [apK_ok_ok, apFlippedK_ok_ok]
    | err e he => rw [apK_ok_err, apFlippedK_err_right]
  · cases f with
    | ok f' => rw [apK_ok_ok, apFlippedK_ok_ok]
    | err e he => rw [apK_err_left, apFlippedK_ok_err]

-- ---------------------------------------------------------------------
-- Instantiating `apK` at the exact union `Grade.join g h`, along the same
-- two inclusions `Graded.ap` itself uses, recovers `ap` — the applicative
-- mirror of `bind_eq_bindK`.
/-- BRIDGE -/
theorem ap_eq_apK (f : Graded g (α → β)) (x : Graded h α) :
    ap f x = apK (Grade.le_join_left g h) (Grade.le_join_right g h) f x := by
  cases f using Graded.rec' with
  | ok f' =>
    cases x using Graded.rec' with
    | ok a => rw [ap_ok_ok, apK_ok_ok]
    | err e he => rw [ap_ok_err, apK_ok_err]
  | err e he => rw [ap_err_left, apK_err_left]

end Graded
