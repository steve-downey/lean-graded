import Graded.AccumTraverse

/-! The per-kind evidence carrier, and what the list carrier owes it.

    **Where this comes from.** [probe-corpus] ran the harness against the
    vendored transpose and found that its accumulating object does not
    store what `Graded.Accum` stores. `Accum` keeps a *list* of errors in
    source order and `toGraded` takes the head. transpose's `error_set`
    value keeps one witness *per kind*, left-biased, laid out in the
    canonical order of the kinds: which kind failed first is not recorded.
    So the harness's `first_error` named a projection the implementation
    cannot compute, and `toGraded_traverseK`/`toGraded_apK` were rows
    without a checkable equation. This module states the carrier the C++
    actually has, the projection from `Accum` onto it, and the laws that
    *do* survive the projection — which are the ones the corpus checks.

    **The carrier.** `Kinds g α` is a value, or a nonempty set of kinds
    `ks ⊆ g`. The evidence is itself a `Grade Err`: the C++ `error_set`
    *value* is a nonempty sub-grade of the `error_set` *type*, and
    combining evidence is `Grade.join`. That is why the applicative laws
    below cite the same lemmas the grade algebra does, and why the
    both-fail leaf of `Kinds.apK_comp` cites `Grade.join_assoc` where
    `Accum.apK_comp` had to cite `List.append_assoc`.

    **Tag-only, deliberately.** At this model's signature a kind carries no
    payload, so "the witness kept for kind `e`" is just "`e` is present";
    the left-bias that decides *which* witness of a repeated kind survives
    is invisible here and belongs to the payload-bearing accumulation
    listed at `docs/design.md#payloads`. What this module can say is
    exactly what the tag-only `Accum` can be asked: which kinds failed,
    and how the short-circuiting projection relates to that set.

    **The finding, as a theorem.** `Kinds.noFirstError`: no function of
    the per-kind evidence recovers `toGraded`, because two lists that
    differ only in order project to the same evidence and to different
    first errors. This is the reason the C++ column of the list-form
    theorems is empty and the per-kind rows exist instead. -/

namespace Graded
namespace Accum
variable {Err : Type u} [DecidableEq Err]
variable {g g' h h' j k : Grade Err} {α β γ : Type v}

/-- A value, or the nonempty set of kinds that failed, each in the grade.
    Models transpose's `error_set` value: one slot per kind of the type's
    grade, at least one filled. The evidence is a `Grade Err` because that
    is what it is — a sub-grade of `g` — and so that combining evidence is
    `Grade.join` and the laws can cite the grade's own lemmas. -/
inductive Kinds (g : Grade Err) (α : Type v)
  | ok     : α → Kinds g α
  | failed : (ks : Grade Err) → ks.Nonempty → ks ⊆ g → Kinds g α

/-- The kinds a result carries: `Grade.bot` for a success. The
    per-kind observation, and the counterpart of `errsOf` for the list
    carrier. -/
def Kinds.kindsOf : Kinds g α → Grade Err
  | .ok _ => Grade.bot
  | .failed ks _ _ => ks

theorem Kinds.kindsOf_ok (a : α) : Kinds.kindsOf (Kinds.ok a : Kinds g α) = Grade.bot := rfl

theorem Kinds.kindsOf_failed (ks : Grade Err) (hne : ks.Nonempty) (hmem : ks ⊆ g) :
    Kinds.kindsOf (Kinds.failed ks hne hmem : Kinds g α) = ks := rfl

/-- Two `failed` values with the same kind set are equal regardless of
    which proofs they carry — the `Kinds` analogue of
    `Accum.errs_eq_of_list_eq`, and the tool every union-of-evidence leaf
    below closes with. -/
theorem Kinds.failed_eq_of_kinds_eq {ks ks' : Grade Err} {hne : ks.Nonempty} {hne' : ks'.Nonempty}
    {hmem : ks ⊆ g} {hmem' : ks' ⊆ g} (heq : ks = ks') :
    (Kinds.failed ks hne hmem : Kinds g α) = Kinds.failed ks' hne' hmem' := by
  subst heq; rfl

def Kinds.map (f : α → β) : Kinds g α → Kinds g β
  | .ok a => .ok (f a)
  | .failed ks hne hmem => .failed ks hne hmem

/-- Subsumption: the evidence is unchanged and gains membership in the
    larger grade — the same conversion for both objects, which is what
    the C++ side found when `toGraded_widen` had nothing to distinguish. -/
def Kinds.widen (h : g ⊆ h') : Kinds g α → Kinds h' α
  | .ok a => .ok a
  | .failed ks hne hmem => .failed ks hne (Grade.le_trans' hmem h)

theorem Kinds.kindsOf_map (f : α → β) (x : Kinds g α) :
    Kinds.kindsOf (Kinds.map f x) = Kinds.kindsOf x := by
  cases x <;> rfl

/-- Widening preserves the evidence exactly: every kind present before is
    present after, and no kind is added. This is the per-kind form of the
    harness's `toGraded_widen` row, and the one the C++ corpus checks. -/
theorem Kinds.kindsOf_widen (h : g ⊆ h') (x : Kinds g α) :
    Kinds.kindsOf (Kinds.widen h x) = Kinds.kindsOf x := by
  cases x <;> rfl

def Kinds.pureK (a : α) : Kinds k α := .ok a

/-- Sequence at a grade `k` containing both, **joining** the evidence when
    both sides fail. Where `Accum.apK` concatenates two lists, this joins
    two sub-grades, and the membership proofs come from `Grade.join_le`
    and `Grade.le_trans'` rather than from list membership. -/
def Kinds.apK (hg : g ⊆ k) (hh : h ⊆ k) (f : Kinds g (α → β)) (x : Kinds h α) : Kinds k β :=
  match f, x with
  | .ok f', .ok a => .ok (f' a)
  | .ok _, .failed ks hne hmem => .failed ks hne (Grade.le_trans' hmem hh)
  | .failed ks hne hmem, .ok _ => .failed ks hne (Grade.le_trans' hmem hg)
  | .failed ks1 hne1 hmem1, .failed ks2 _hne2 hmem2 =>
      .failed (Grade.join ks1 ks2) (hne1.mono (Grade.le_join_left ks1 ks2))
        (Grade.join_le (Grade.le_trans' hmem1 hg) (Grade.le_trans' hmem2 hh))

def Kinds.map2K (hg : g ⊆ k) (hh : h ⊆ k) (f : α → β → γ) (x : Kinds g α) (y : Kinds h β) :
    Kinds k γ :=
  Kinds.apK hg hh (Kinds.map f x) y

/-- **The evidence of an application is the join of the evidence.** Every
    kind either side raised is present, and no other. Cites the unit laws
    for the two one-sided cases, where one side's evidence is `bot`. -/
theorem Kinds.kindsOf_apK (hg : g ⊆ k) (hh : h ⊆ k) (f : Kinds g (α → β)) (x : Kinds h α) :
    Kinds.kindsOf (Kinds.apK hg hh f x) = Grade.join (Kinds.kindsOf f) (Kinds.kindsOf x) := by
  cases f with
  | ok f' => cases x with
    | ok a => exact (Grade.bot_join Grade.bot).symm
    | failed ks hne hmem => exact (Grade.bot_join ks).symm
  | failed ks1 hne1 hmem1 => cases x with
    | ok a => exact (Grade.join_bot ks1).symm
    | failed ks2 hne2 hmem2 => rfl

theorem Kinds.kindsOf_map2K (hg : g ⊆ k) (hh : h ⊆ k) (f : α → β → γ)
    (x : Kinds g α) (y : Kinds h β) :
    Kinds.kindsOf (Kinds.map2K hg hh f x y) = Grade.join (Kinds.kindsOf x) (Kinds.kindsOf y) := by
  rw [Kinds.map2K, Kinds.kindsOf_apK, Kinds.kindsOf_map]

-- ---------------------------------------------------------------------
-- The four applicative laws at a sufficient grade. Three are `rfl` at
-- every leaf, as for `Accum`; composition's both-fail leaves need
-- `Grade.join_assoc`, exactly where `Accum.apK_comp` needed
-- `List.append_assoc`. Same law, same leaf, the grade's own lemma.

theorem Kinds.apK_pure_id (hh : h ⊆ k) (x : Kinds h α) :
    Kinds.apK (Grade.le_refl' k) hh (Kinds.pureK (@id α) : Kinds k (α → α)) x
      = Kinds.widen hh x := by
  cases x <;> rfl

theorem Kinds.apK_pure_pure (f : α → β) (a : α) :
    Kinds.apK (Grade.le_refl' k) (Grade.le_refl' k) (Kinds.pureK f : Kinds k (α → β))
        (Kinds.pureK a)
      = (Kinds.pureK (f a) : Kinds k β) := rfl

theorem Kinds.apK_interchange (hg : g ⊆ k) (u : Kinds g (α → β)) (a : α) :
    Kinds.apK hg (Grade.le_refl' k) u (Kinds.pureK a : Kinds k α)
      = Kinds.apK (Grade.le_refl' k) hg
          (Kinds.pureK (fun f => f a) : Kinds k ((α → β) → β)) u := by
  cases u <;> rfl

theorem Kinds.apK_comp (hg : g ⊆ k) (hg' : g' ⊆ k) (hj : j ⊆ k)
    (u : Kinds g (β → γ)) (v : Kinds g' (α → β)) (w : Kinds j α) :
    Kinds.apK (Grade.le_refl' k) hj (Kinds.apK (Grade.le_refl' k) hg'
        (Kinds.apK (Grade.le_refl' k) hg
          (Kinds.pureK Function.comp : Kinds k ((β → γ) → (α → β) → α → γ)) u)
        v) w
      = Kinds.apK hg (Grade.le_refl' k) u (Kinds.apK hg' hj v w) := by
  cases u with
  | ok u' =>
      cases v with
      | ok v' => cases w <;> rfl
      | failed kv hnev hmemv =>
          cases w <;> [rfl; exact Kinds.failed_eq_of_kinds_eq rfl]
  | failed ku hneu hmemu =>
      cases v with
      | ok v' => cases w <;> [rfl; exact Kinds.failed_eq_of_kinds_eq rfl]
      | failed kv hnev hmemv =>
          cases w <;> [exact Kinds.failed_eq_of_kinds_eq rfl;
                       exact Kinds.failed_eq_of_kinds_eq (Grade.join_assoc ku kv _)]

-- ---------------------------------------------------------------------
-- Traversal, shaped like `Accum.traverseK`.

def Kinds.traverseK (hg : g ⊆ k) (f : α → Kinds g β) : List α → Kinds k (List β)
  | []      => Kinds.pureK []
  | x :: xs => Kinds.map2K hg (Grade.le_refl' k) (fun b bs => b :: bs) (f x)
                 (Kinds.traverseK hg f xs)

theorem Kinds.traverseK_nil (hg : g ⊆ k) (f : α → Kinds g β) :
    Kinds.traverseK hg f ([] : List α) = Kinds.pureK [] := rfl

theorem Kinds.traverseK_cons (hg : g ⊆ k) (f : α → Kinds g β) (x : α) (xs : List α) :
    Kinds.traverseK hg f (x :: xs)
      = Kinds.map2K hg (Grade.le_refl' k) (fun b bs => b :: bs) (f x)
          (Kinds.traverseK hg f xs) := rfl

/-- The evidence of a traversal is the join of each position's evidence,
    folded right. -/
theorem Kinds.kindsOf_traverseK (hg : g ⊆ k) (f : α → Kinds g β) (xs : List α) :
    Kinds.kindsOf (Kinds.traverseK hg f xs)
      = xs.foldr (fun x acc => Grade.join (Kinds.kindsOf (f x)) acc) Grade.bot := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [Kinds.traverseK_cons, Kinds.kindsOf_map2K, ih, List.foldr_cons]

/-- **A kind is present exactly when some position raised it.** The
    per-kind form of `errsOf_traverseK`: every failing position
    contributes its kinds, no succeeding position contributes anything,
    and — unlike the list — a kind raised at two positions is present
    once. This is the row the C++ corpus checks. -/
theorem Kinds.mem_kindsOf_traverseK (hg : g ⊆ k) (f : α → Kinds g β) (xs : List α) (e : Err) :
    e ∈ Kinds.kindsOf (Kinds.traverseK hg f xs) ↔ ∃ x ∈ xs, e ∈ Kinds.kindsOf (f x) := by
  induction xs with
  | nil => simp [Kinds.traverseK_nil, Kinds.pureK, Kinds.kindsOf, Grade.bot]
  | cons x xs ih =>
      rw [Kinds.traverseK_cons, Kinds.kindsOf_map2K, Grade.join, Finset.mem_union, ih]
      simp only [List.mem_cons, exists_eq_or_imp]

/-- Success is `List.map`, as for the list carrier. -/
theorem Kinds.traverseK_ok (hg : g ⊆ k) (f : α → Kinds g β) (fo : α → β)
    (hf : ∀ a, f a = Kinds.ok (fo a)) (xs : List α) :
    Kinds.traverseK hg f xs = Kinds.ok (xs.map fo) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [Kinds.traverseK_cons, Kinds.map2K, ih, hf x]; rfl

-- ---------------------------------------------------------------------
-- The projection from the list carrier: forget the order, keep the set.
-- One direction only; `noFirstError` at the end is why.

/-- Forget the order of an accumulated list, keeping which kinds occur.
    This is what the C++ accumulating object does at every combination
    step, and the *only* thing it retains. -/
def Kinds.ofAccum : Accum g α → Kinds g α
  | .ok a => .ok a
  | .errs es hne hmem =>
      .failed es.toFinset ⟨es.head hne, List.mem_toFinset.mpr (List.head_mem hne)⟩
        (fun e he => hmem e (List.mem_toFinset.mp he))

theorem Kinds.ofAccum_ok (a : α) : Kinds.ofAccum (Accum.ok a : Accum g α) = Kinds.ok a := rfl

theorem Kinds.ofAccum_errs (es : List Err) (hne : es ≠ []) (hmem : ∀ e ∈ es, e ∈ g) :
    Kinds.ofAccum (Accum.errs es hne hmem : Accum g α)
      = Kinds.failed es.toFinset ⟨es.head hne, List.mem_toFinset.mpr (List.head_mem hne)⟩
          (fun e he => hmem e (List.mem_toFinset.mp he)) := rfl

/-- The kinds of the projection are the kinds in the list. -/
theorem Kinds.kindsOf_ofAccum (x : Accum g α) :
    Kinds.kindsOf (Kinds.ofAccum x) = (errsOf x).toFinset := by
  cases x with
  | ok a => rfl
  | errs es hne hmem => rfl

theorem Kinds.ofAccum_map (f : α → β) (x : Accum g α) :
    Kinds.ofAccum (Accum.map f x) = Kinds.map f (Kinds.ofAccum x) := by
  cases x <;> rfl

theorem Kinds.ofAccum_widen (h : g ⊆ h') (x : Accum g α) :
    Kinds.ofAccum (Accum.widen h x) = Kinds.widen h (Kinds.ofAccum x) := by
  cases x <;> rfl

theorem Kinds.ofAccum_pureK (a : α) :
    Kinds.ofAccum (Accum.pureK a : Accum k α) = Kinds.pureK a := rfl

/-- **The projection is an applicative morphism.** Concatenating two lists
    and then taking the set is joining the two sets: `List.toFinset_append`
    at the both-fail leaf, and `rfl` everywhere else. This is the fact
    that lets the C++ combine per kind at every step and still agree with
    the model's list at the end. -/
theorem Kinds.ofAccum_apK (hg : g ⊆ k) (hh : h ⊆ k) (f : Accum g (α → β)) (x : Accum h α) :
    Kinds.ofAccum (Accum.apK hg hh f x) = Kinds.apK hg hh (Kinds.ofAccum f) (Kinds.ofAccum x) := by
  cases f with
  | ok f' => cases x with
    | ok a => rfl
    | errs es hne hmem => rfl
  | errs es1 hne1 hmem1 => cases x with
    | ok a => rfl
    | errs es2 hne2 hmem2 =>
        exact Kinds.failed_eq_of_kinds_eq (List.toFinset_append)

theorem Kinds.ofAccum_map2K (hg : g ⊆ k) (hh : h ⊆ k) (f : α → β → γ)
    (x : Accum g α) (y : Accum h β) :
    Kinds.ofAccum (Accum.map2K hg hh f x y)
      = Kinds.map2K hg hh f (Kinds.ofAccum x) (Kinds.ofAccum y) := by
  rw [Accum.map2K, Kinds.map2K, Kinds.ofAccum_apK, Kinds.ofAccum_map]

/-- The projection commutes with traversal: accumulate the list and forget
    the order, or accumulate the sets from the start. -/
theorem Kinds.ofAccum_traverseK (hg : g ⊆ k) (f : α → Accum g β) (xs : List α) :
    Kinds.ofAccum (Accum.traverseK hg f xs)
      = Kinds.traverseK hg (fun a => Kinds.ofAccum (f a)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [Accum.traverseK_cons, Kinds.traverseK_cons, Kinds.ofAccum_map2K, ih]

-- ---------------------------------------------------------------------
-- What the short-circuiting projection and the per-kind projection say
-- about each other. Two facts survive, and one does not.

/-- **The kind the short-circuiting carrier kept is present in the
    per-kind evidence.** This is what remains of `toGraded_traverseK` and
    `toGraded_apK` once the order is forgotten, and it is what the C++
    corpus checks: whatever kind the fail-fast result carries, the
    accumulating result holds that kind too. -/
theorem Kinds.toGraded_mem (x : Accum g α) (e : Err) (he : e ∈ g)
    (hx : toGraded x = Graded.err e he) :
    e ∈ Kinds.kindsOf (Kinds.ofAccum x) := by
  cases x with
  | ok a => exact absurd hx Graded.ok_ne_err
  | errs es hne hmem =>
      cases es with
      | nil => exact absurd rfl hne
      | cons e' es' =>
          rw [toGraded_errs, Graded.err_eq_err] at hx
          subst hx
          exact List.mem_toFinset.mpr List.mem_cons_self

/-- **With exactly one kind present, the two carriers agree outright.**
    When the per-kind evidence is a singleton, the short-circuiting
    carrier holds that kind — the case the C++ corpus checks by comparing
    the two results for equality when one operand fails. -/
theorem Kinds.toGraded_of_kindsOf_singleton (x : Accum g α) (e : Err)
    (hk : Kinds.kindsOf (Kinds.ofAccum x) = {e}) :
    ∃ he : e ∈ g, toGraded x = Graded.err e he := by
  cases x with
  | ok a => exact absurd hk.symm (Finset.singleton_ne_empty e)
  | errs es hne hmem =>
      cases es with
      | nil => exact absurd rfl hne
      | cons e' es' =>
          have hmem' : e' ∈ Kinds.kindsOf
              (Kinds.ofAccum (Accum.errs (e' :: es') hne hmem : Accum g α)) :=
            List.mem_toFinset.mpr List.mem_cons_self
          rw [hk, Finset.mem_singleton] at hmem'
          subst hmem'
          exact ⟨hmem e' List.mem_cons_self, rfl⟩

/-- **There is no `first_error`.** No function of the per-kind evidence
    recovers the short-circuiting carrier, for any projection that is
    uniform in the grade and the payload type: the lists `[e₁, e₂]` and
    `[e₂, e₁]` forget to the same set and short-circuit to different
    errors. This is [probe-corpus]'s finding, stated in the model rather
    than in a comment: the harness's `first_error` was not an operation
    the C++ carrier could have, and the rows that assumed it now carry
    `Kinds.toGraded_mem` and `Kinds.toGraded_of_kindsOf_singleton`
    instead. -/
theorem Kinds.noFirstError (e₁ e₂ : Err) (hne : e₁ ≠ e₂) :
    ¬ ∃ proj : ∀ {g : Grade Err} {α : Type v}, Kinds g α → Graded g α,
        ∀ {g : Grade Err} {α : Type v} (x : Accum g α), proj (Kinds.ofAccum x) = toGraded x := by
  rintro ⟨proj, hproj⟩
  let g : Grade Err := {e₁, e₂}
  have h₁ : e₁ ∈ g := by simp [g]
  have h₂ : e₂ ∈ g := by simp [g]
  let x₁ : Accum g PUnit.{v + 1} :=
    Accum.errs [e₁, e₂] (List.cons_ne_nil e₁ [e₂])
      (fun e he => by
        rcases List.mem_cons.mp he with rfl | he'
        · exact h₁
        · rcases List.mem_singleton.mp he' with rfl
          exact h₂)
  let x₂ : Accum g PUnit.{v + 1} :=
    Accum.errs [e₂, e₁] (List.cons_ne_nil e₂ [e₁])
      (fun e he => by
        rcases List.mem_cons.mp he with rfl | he'
        · exact h₂
        · rcases List.mem_singleton.mp he' with rfl
          exact h₁)
  have hsame : Kinds.ofAccum x₁ = Kinds.ofAccum x₂ :=
    Kinds.failed_eq_of_kinds_eq (by
      simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
      exact Finset.pair_comm e₁ e₂)
  have h := hproj x₁
  rw [hsame, hproj x₂] at h
  -- `h : toGraded x₂ = toGraded x₁`, i.e. `err e₂ = err e₁`.
  have h' : (Graded.err e₂ h₂ : Graded g PUnit.{v + 1}) = Graded.err e₁ h₁ := h
  exact hne (Graded.err_eq_err.mp h').symm

end Accum
end Graded
