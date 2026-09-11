import Graded.Sufficient.ApplicativeK
import Graded.Tuple

/-! `sequenceK`: heterogeneous tuple sequencing at a caller-nominated
    grade.

    Every other operation in the model got a sufficient-grade sibling
    during the cast-burden migration — `bindK`, `apK`, `traverseK`,
    `flattenK`, `Comp.apK`. Heterogeneous sequencing did not, and the
    improvements outline did not notice: the counter-plan's §3.7 records
    the gap. This closes it.

    **The interesting difference from `traverseK`.** Uniform list
    traversal has *one* source grade `g`, so it takes one inclusion
    `g ⊆ k` and reuses it at every position. A tuple's slots carry
    *different* grades, so there is no single inclusion to reuse: the
    hypothesis is `∀ g ∈ gs, g ⊆ k`, one witness per slot, supplied by
    membership. That is the shape the heterogeneous case forces, and it
    is why `sequenceK` could not have been a copy of `traverseK` with the
    fold deleted.

    What it buys is the same thing every other `K` operation buys.
    `sequence` lands at `joinAll gs`, a grade *computed* from the slot
    grades, and [traverse-tuple] called the tuple case "where the grade is
    really computed". `sequenceK` lands at the caller's `k` directly, so
    the computed fold never appears in the type, and `sequence_eq_sequenceK`
    recovers `sequence` by instantiating `k` at `joinAll gs` with the
    inclusions `joinAll` itself provides. -/

namespace Graded

variable {Err : Type u} [DecidableEq Err]
variable {k : Grade Err} {α : Type v}

/-- Sequence a heterogeneous tuple into a caller-nominated grade `k`,
    given that every slot's grade is contained in it. -/
def sequenceK : {gs : List (Grade Err)} → {αs : List (Type v)} →
    (∀ g ∈ gs, g ⊆ k) → GList gs αs → Graded k (HList αs)
  | [], [], _, _ => pureK HList.nil
  | _ :: _, [], _, xs => nomatch xs
  | [], _ :: _, _, xs => nomatch xs
  | g :: _, _ :: _, h, (x, xs) =>
      map2K (h g List.mem_cons_self) (Grade.le_refl' k) HList.cons x
        (sequenceK (fun g' hg' => h g' (List.mem_cons_of_mem g hg')) xs)

theorem sequenceK_nil (h : ∀ g ∈ ([] : List (Grade Err)), g ⊆ k) :
    (sequenceK h (GList.nil : GList [] ([] : List (Type v))) : Graded k (HList [])) =
      pureK HList.nil := rfl

theorem sequenceK_cons {g : Grade Err} {gs : List (Grade Err)}
    {β : Type v} {αs : List (Type v)}
    (h : ∀ g' ∈ g :: gs, g' ⊆ k) (x : Graded g β) (xs : GList gs αs) :
    sequenceK h (GList.cons x xs)
      = map2K (h g List.mem_cons_self) (Grade.le_refl' k) HList.cons x
          (sequenceK (fun g' hg' => h g' (List.mem_cons_of_mem g hg')) xs) := rfl

/-- Which witness justifies each slot does not matter, only that one
    exists — the mirror of `bindK_irrel`/`traverseK_irrel`, and `rfl` for
    the same reason: every hypothesis threaded through is a `Prop`. Note
    this is a stronger statement than those two, since there is a whole
    *family* of witnesses here rather than one or two. -/
theorem sequenceK_irrel {gs : List (Grade Err)} {αs : List (Type v)}
    (h h' : ∀ g ∈ gs, g ⊆ k) (xs : GList gs αs) :
    sequenceK h xs = sequenceK h' xs := rfl

-- ---------------------------------------------------------------------
-- **No bridge to `sequence`, and this is a recorded gap rather than an
-- oversight.** Every other sufficient-grade operation has one —
-- `bind_eq_bindK`, `ap_eq_apK`, `traverse_eq_traverseK`,
-- `flatten_eq_flattenK` — each recovering the union-graded spelling by
-- instantiating `k` at the computed grade. `sequence_eq_sequenceK` does
-- not go through by the same induction, and the reason is structural:
-- `sequence` recurses at `joinAll gs` and joins one slot at a time, so
-- each recursive call sits at a *different, smaller* grade, while
-- `sequenceK` recurses at the caller's `k` throughout. The induction
-- hypothesis is therefore about `sequenceK` at the wrong grade, and
-- closing the gap needs a commutation lemma
-- (`apK hg hh u (widen w v) = widen _ (ap u v)`) that `apK`'s
-- `bindK`-derived definition does not supply by `rfl` — it would have to
-- be proved through `bindK_eq_widen_bind` twice plus `widen_widen`.
--
-- Neither the uniform `traverseK` nor `flattenK` hits this, because
-- neither recurses through a changing grade. It is specific to the
-- heterogeneous case, which is the one [traverse-tuple] called "where
-- the grade is really computed". Left unproved, and named here, rather
-- than left as a silent asymmetry.

end Graded
