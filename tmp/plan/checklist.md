# Checklist — Lean model of graded Transpose

Ordinal is reading order; slug is identity. Cross-reference by slug only.
Mark your own step done before writing the next step's handoff.

- [x] 1. [baseline-capture](step-baseline-capture.md)
- [x] 2. [grade-pomonoid](step-grade-pomonoid.md)
- [x] 3. [graded-carrier](step-graded-carrier.md)
- [x] 4. [subsumption-widen](step-subsumption-widen.md)
- [x] 5. [monad-laws](step-monad-laws.md)
- [x] 6. [applicative-from-monad](step-applicative-from-monad.md)
- [x] 7. [applicative-accumulation](step-applicative-accumulation.md)
- [x] 8. [traverse-list](step-traverse-list.md)
- [x] 9. [traverse-tuple](step-traverse-tuple.md)
- [x] 10. [compose-flatten](step-compose-flatten.md) — partial: flattened traverse composition law refuted, product-graded case untested, see [graded-traversable-composition](../../docs/design.md#graded-traversable-composition)
- [x] 11. [graded-morphism](step-graded-morphism.md)
- [x] 12. [canonical-representation](step-canonical-representation.md)
- [x] 13. [compose-applicative](step-compose-applicative.md) — product-graded composition law (`traverseComp_eq`) holds unconditionally; `flatten_ap` holds only conditionally and explains [compose-flatten]'s counterexample; [graded-traversable-composition](../../docs/design.md#graded-traversable-composition) now CLOSED
- [x] 14. [ungraded-baseline](step-ungraded-baseline.md) — added 2026-09-08: the comparison column, what grading adds; monad/applicative laws cast-free at a fixed grade, idempotence only; `sumEquiv` transport to Mathlib's `Sum` proved; flattened composition re-confirmed false at a fixed grade
- [x] 15. [grade-obligations](step-grade-obligations.md) — added 2026-09-08: what a grade must be, layered, with a non-idempotent counter-instance; `foldG_le` needed `IsIdemPomonoid`, not `Pomonoid` alone as predicted — see [obligations](../../docs/design.md#obligations)
- [x] 16. [oracle-export](step-oracle-export.md) — added 2026-09-08: mechanical law inventory (146 theorems) with pomonoid properties and C++ probe list; corrected the plan's own predictions — commutativity is six sites not three, the at-most-one-error condition is four sites and not the same finding four times, `foldG_le`'s table row is honestly incomplete pending [grade-join-strength](../../docs/design.md#grade-join-strength)
- [x] 17. [blog-series-edit](step-blog-series-edit.md) — closing.org numbered Letter 16, not the literally-stated 17 (fixed a systematic off-by-one self-numbering bug in the existing letters instead); see [handoff-integration-review](handoff-integration-review.md)
- [ ] 18. [integration-review](INTEGRATION-REVIEW.md) — scoped `model: opus` consult, not a Sonnet worker
