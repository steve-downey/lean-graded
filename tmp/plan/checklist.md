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
- [x] 18. [integration-review](INTEGRATION-REVIEW.md) — cross-step coherence GREEN; findings in §6. The three doc/code defects it named (`join_comm` "second appearance" at five sites, `#provisional-decisions` missing `#grade`, two `Canonical.lean` rules violations, and an untested commutativity path) were fixed in `94bd0b8`; the `#carrier` cast verdict being overtaken by `ComposeApp` is addressed by steps 19-20 below. Metrics promoted to `metrics/fanout-runs.jsonl`

Follow-up run, planned 2026-09-08 after the integration review found the
cast burden had outgrown [monad-laws]'s verdict. Step 20 is gated on 19's
measured verdict; the remainder is the open question
[cast-burden-migration-scope](../../docs/design.md#cast-burden-migration-scope).

- [x] 19. [sufficient-grade-bind](step-sufficient-grade-bind.md) — `bindK` beside `bind`, cast-free laws, `bind_eq_bindK` bridge closes by `rfl`, `bindK_irrel` free by `rfl`; verdict: worth extending to the applicative layer
- [x] 20. [sufficient-grade-applicative](step-sufficient-grade-applicative.md) — `apK`/`map2K`/`Comp.apK` cast-free, `Comp.ap_interchange`'s six-cast analogue now zero; `apK_flip` needs no `Grade.join_comm` — commutativity was a cost of computing the grade exactly, not the applicative; see [cast-burden-migration-scope](../../docs/design.md#cast-burden-migration-scope)
- [x] 21. [obligation-layering](step-obligation-layering.md) — classified all 14 non-defining `join_comm`/`join_idem` consumers as canonicalization (grade-spelling), none operational; hypothesis holds — `Pomonoid` is the whole operational obligation; `IsCommPomonoid`/`IsIdemPomonoid` decoupled to siblings, `IsCanonicalPomonoid` added as the named bundle; `join_le`/`foldG_le` are grade-boundedness facts, not operational, but sharpen rather than close [grade-join-strength](../../docs/design.md#grade-join-strength)
- [x] 22. [sufficient-grade-traverse](step-sufficient-grade-traverse.md) — the fold disappeared entirely: no `foldGradeK`, every `traverseK` analogue cites no pomonoid property at all; `traverse_eq_traverseK` bridges cleanly, paying `Grade.join_idem` once on the union-graded side only
- [x] 23. [sufficient-grade-morphism](step-sufficient-grade-morphism.md) — the morphism leg; a grade morphism need only be monotone, not a homomorphism; the bridge from `GradedHom` is one-directional and stops at `gmap_mono` alone, since `hom` is never asked to commute with `widen`; built the monotone-but-not-homomorphism counter-instance
- [ ] 24. [sufficient-grade-nested](step-sufficient-grade-nested.md) — the nested carriers; **closes** [cast-burden-migration-scope](../../docs/design.md#cast-burden-migration-scope)
