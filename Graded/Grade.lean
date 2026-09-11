import Graded.Prelude
import Mathlib.Data.Finset.Lattice.Lemmas

/-! The grade: a finite set of error kinds, joined by union and ordered by
    inclusion. Every pomonoid property it has is stated below as a
    separately named lemma, so later steps can cite exactly the property
    each law depends on. -/

namespace Graded

/-- A grade is a finite set of error *kinds*. `Err` plays the role of the
    universe of C++ error types; `DecidableEq` is what lets us form sets. -/
abbrev Grade (Err : Type u) [DecidableEq Err] := Finset Err

namespace Grade
variable {Err : Type u} [DecidableEq Err]

def bot : Grade Err := ∅
def join (g h : Grade Err) : Grade Err := g ∪ h
-- order is `⊆`, written `g ≤ h` via Finset's PartialOrder; state the
-- lemmas below against `⊆` so C++ readers see "subset".

/-- PROPERTY: associative -/
theorem join_assoc (g h k : Grade Err) : join (join g h) k = join g (join h k) :=
  Finset.union_assoc g h k

/-- PROPERTY: commutative -/
theorem join_comm (g h : Grade Err) : join g h = join h g :=
  Finset.union_comm g h

/-- PROPERTY: idempotent -/
theorem join_idem (g : Grade Err) : join g g = g :=
  Finset.union_idempotent g

/-- PROPERTY: unit -/
theorem bot_join (g : Grade Err) : join bot g = g :=
  Finset.empty_union g

/-- PROPERTY: unit -/
theorem join_bot (g : Grade Err) : join g bot = g :=
  Finset.union_empty g

theorem le_join_left (g h : Grade Err) : g ⊆ join g h :=
  Finset.subset_union_left

theorem le_join_right (g h : Grade Err) : h ⊆ join g h :=
  Finset.subset_union_right

theorem join_le {g h k : Grade Err} (hg : g ⊆ k) (hh : h ⊆ k) : join g h ⊆ k :=
  Finset.union_subset hg hh

theorem join_mono {g g' h h' : Grade Err} (hg : g ⊆ g') (hh : h ⊆ h') :
    join g h ⊆ join g' h' :=
  Finset.union_subset_union hg hh

/-- PROPERTY: order -/
theorem le_refl' (g : Grade Err) : g ⊆ g :=
  Finset.Subset.refl g

/-- PROPERTY: order -/
theorem le_trans' {g h k : Grade Err} (hgh : g ⊆ h) (hhk : h ⊆ k) : g ⊆ k :=
  Finset.Subset.trans hgh hhk

theorem bot_le (g : Grade Err) : bot ⊆ g :=
  Finset.empty_subset g

/-- PROPERTY: antisymmetry -/
theorem le_antisymm {g h : Grade Err} (hgh : g ⊆ h) (hhg : h ⊆ g) : g = h :=
  Finset.Subset.antisymm hgh hhg

theorem join_eq_right_of_le {g h : Grade Err} (hgh : g ⊆ h) : join g h = h :=
  Finset.union_eq_right.mpr hgh

end Grade
end Graded
