import Mathlib.Data.Finset.Basic

/-! Shared imports and the `Graded` namespace. Later steps add modules
    here and to `Graded.lean`. -/

namespace Graded

/-- A heterogeneous list ("tuple"), indexed by the list of its elements'
    payload types: `HList [] = PUnit`, `HList (α :: αs) = α × HList αs`.
    Checked against Mathlib at the pinned version ([traverse-tuple]) before
    writing this: `List.TProd` (`Mathlib.Data.Prod.TProd`) builds the same
    kind of iterated product, but over an arbitrary index type `ι` and a
    family `π : ι → Type*` — using it here would mean instantiating `ι :=
    Type v`, `π := id`, which buys nothing over a direct three-line `def`
    and loses the `HList.nil`/`HList.cons` names this module's consumer
    (`Graded.Tuple.sequence`) pattern their equations on. Written fresh,
    as a shared definition, since every later module imports this file. -/
def HList : List (Type v) → Type v
  | [] => PUnit
  | α :: αs => α × HList αs

/-- The empty heterogeneous tuple. -/
def HList.nil : HList ([] : List (Type v)) := PUnit.unit

/-- Extend a heterogeneous tuple with one more element at the front. Not a
    constructor of an inductive type — `HList` is the plain recursive
    product above — but named `cons` to match `GList.cons`'s shape, since
    `Graded.Tuple.sequence_cons` states its equation with this name. -/
def HList.cons {α : Type v} {αs : List (Type v)} (a : α) (t : HList αs) : HList (α :: αs) :=
  ⟨a, t⟩

end Graded
