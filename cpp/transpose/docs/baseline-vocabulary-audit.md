# Baseline vocabulary audit

Deliverable of stage [baseline-capture](transpose-grading-plan.md#baseline-capture), which asks: grep the public surface, and classify every mention of error machinery as grade-vocabulary (framework) or error-vocabulary (model), per [grade-generality](decisions.md#grade-generality).

Audited at commit `672b890`, the state of `main` before any grading work.
The companion mechanical deliverable is `tests/beman/transpose/baseline_deduction.test.cpp`.

## Method

The audited surface is every header under `include/beman/transpose/`, which is the whole public surface: the library is header-only and installs exactly this tree.

```sh
grep -rniE "error|fail|exception|throw|unexpected|bad_|errc|status|diagnos" \
    include/beman/transpose/*.hpp include/beman/transpose/detail/*.hpp
grep -rniE "grade|semilattice|join|bottom|subsume|lattice|union" \
    include/beman/transpose/*.hpp include/beman/transpose/detail/*.hpp
grep -rn "expected" include tests examples
```

## Finding: the surface carries no error vocabulary at all

The error-machinery grep returns four hits, all in comments, and none of them are about errors in the sense grading means.

| Location | Text | Classification |
| --- | --- | --- |
| `apply.hpp:87` | "fails cleanly -- never hard-errors" | Neither. Compile-time SFINAE prose. |
| `apply.hpp:131` | "availability probes fail cleanly instead of hard-erroring" | Neither. Compile-time SFINAE prose. |
| `apply.hpp:340` | "probes fail cleanly" | Neither. Compile-time SFINAE prose. |
| `simd.hpp:35` | "every probe fails cleanly (SFINAE)" | Neither. Compile-time SFINAE prose. |

Every hit describes *constraint satisfaction*, not a value-level failure channel.
There is no runtime error concept anywhere on the surface: no `expected`, no `error_type`, no exception vocabulary, no failure alternative in any carrier.
`std::optional`'s disengaged state is the only failure-shaped thing in the library, and it is untyped by construction.

The classification exercise is therefore vacuous in the best way.
The framework/model boundary that [grade-generality](decisions.md#grade-generality) requires — grade vocabulary in the framework layer, error vocabulary confined to the model layer — starts from an empty ledger.
No existing name has to be moved, renamed, or re-homed to establish it.

## Finding: `expected` is absent from the entire repository

The third grep returns nothing, in `include/`, `tests/`, and `examples/` alike.

`std::expected` is not a registered applicative, monad, or functor.
The plan's §1 treats `expected<T, error_set<A,B>>` as *the* carrier, and [grading-footprint](decisions.md#grading-footprint) frames the newly-well-formed territory as "mixing `expected<T,E1>` with `expected<T,E2>`".
Both readings assume an ungraded `expected` instance exists to be extended.
It does not.

This is recorded as a divergence under [grading-footprint](decisions.md#grading-footprint) and as the open question [expected-instance-introduction](decisions.md#expected-instance-introduction).
The golden tests pin the absence explicitly, so that a later stage flipping `expected` to registered is a deliberate act rather than an accident.

The *structure* side is ready even though the context side is empty: `std::vector<std::expected<T,E>>` is already a registered traversable, and `applicative_value_t` already extracts `T` from `std::expected<T,E>` through its nested `value_type`, with no specialization needed.
Only the context side is missing.

## Finding: `join` is already taken

The grade-vocabulary grep returns six hits, all of them one name: `join`.

`beman::transpose::join(MMA&&)` (`monad.hpp:154`) and `Monad::join` (`monad.hpp:84`) are the monadic join — flatten a nested monad, `join mma = mma >>= id`.
This is the standard meaning and it is load-bearing in the Monad instance.

[grade-machinery-home](decisions.md#grade-machinery-home) gives the grade algebra an operation also called `join` (the semilattice `∪`).
Both would live in `beman::transpose`.
The collision is real but shallow — it is a spelling question, not a design one, and it is cheapest to settle before Stage [grade-concept](transpose-grading-plan.md#grade-concept) writes the name down.
Raised as [grade-operation-spelling](decisions.md#grade-operation-spelling).

No other grade vocabulary is in use: `grade`, `semilattice`, `bottom`, `subsume`, and `lattice` return zero hits.

## Public surface inventory

For completeness, the full set of namespace-scope public entities, none of which mention errors:

- Typeclass CRTP bases: `Functor`, `Applicative`, `Monad`, `Foldable`, `Traversable`, `Monoid`.
- Lookup variable templates: `functor_typeclass`, `applicative_typeclass`, `monad_typeclass`, `foldable_typeclass`, `traversable_typeclass`, `monoid_v`.
- Free verbs: `traverse`, `transpose`, `transpose_tuple`, `mbind`, `join`, `monoid_identity`, `monoid_combine`.
- Traits: `remove_cvref_t`, `applicative_value` / `applicative_value_t`.
- Carriers and their instances: `std::optional`, `std::vector`, `std::array`, `sender`, `zip_list`, and the SIMD lane types behind `__has_include(<simd>)`.

## Tripwire check

Stage [baseline-capture](transpose-grading-plan.md#baseline-capture) says to STOP if current behavior already violates a standing decision.
It does not.
Nothing normalizes eagerly, nothing carries a grade, and no carrier has a typed failure channel that grading would have to reconcile with.
The tripwire did not fire.
