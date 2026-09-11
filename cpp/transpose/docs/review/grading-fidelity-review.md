# Design-Fidelity Review — Grading Branch (interim, pre-delivery)

Reviewed at commit `e955c62` ("Stage model-dispatched-mixing repair") by a
fresh agent working only from `docs/transpose-grading-plan.md`,
`docs/decisions.md`, the branch history, and the review brief. Read-only:
no code, no `decisions.md` edits; proposed log entries are drafts for Steve
to integrate.

Method note: the review environment has no gcc-16, so the branch build was
not re-run. All findings come from reading the code and history, plus one
targeted compile probe (finding A-1) built with clang-18 against the shipped
headers; the probe's source is reproduced in that finding.

## Boot check

All 18 DECIDED and 3 OPEN slugs were enumerated before code was read; no two
decisions conflict as written. The two near-conflicts —
`plain-error-grade-reading` vs. `grading-footprint`'s lazy join, and
`bottom-grade-identity` vs. `empty-grade-spelling` — are each reconciled
inside the entries themselves. Inter-document drift found before touching
code is filed under class D.

## Direction 1 — decision → embodiment → sensor

| Slug | Embodiment | Sensor |
|---|---|---|
| empty-grade-spelling | `error_set.hpp:919-928` (`rebind_grade` at `error_set<>` strips to bare `T`); `error_set.hpp:468-477` (`error_set_of<>` uninhabited) | `grade.test.cpp:147-155`; `laws.hpp:264-270` (generalized over every model); `crtp_absorption.test.cpp:149-154`; `accumulating_object.test.cpp:351-354`; `baseline_deduction.test.cpp:270` (`!applicative_registered<int>`) |
| grading-footprint | `expected.hpp:85-104` (complementary constraints `all_declare_v` / `all_declare_or_bare_v` and their negations on the three cores) | `baseline_deduction.test.cpp` §§1–8 (unchanged deductions) and §9 lazy-join controls; `expected.test.cpp` "bare operand … leaves no trace" |
| error-set-identity | `error_set.hpp:281-448` (nominal class, canonical alias `:481-483`, ⊆-only ctors `:314-322`, defaulted `==` `:394`) | `error_set.test.cpp:54-69` (canonical alias identity, incl. `error_set<A,B>` ≡ `error_set<B,A>`), `:137-165` (⊆-only, negatives both directions), `:282-298` (equality) |
| grade-machinery-home | `grade.hpp:110-137` (traits, ∅ default); CRTP `subsume` `apply.hpp:323-330`, `monad.hpp:133-140`; ap-from-bind `monad.hpp:110-125` | `crtp_absorption.test.cpp` (zero-grade-awareness instance gets full surface); `grade.test.cpp:97-104` (∅ default on every baseline matrix type). See D-4 for one drifted sentence |
| applicative-objects | `apply.hpp:361-379` (second lookup point); `expected.hpp:328-491`; bind refused with value-flow diagnostic `expected.hpp:472-483` | `accumulating_object.test.cpp:90-92` (distinct objects), order/left-bias probes `:126-151`, hand-verified bind negative `:242-275` (see C-2) |
| recover-grade-inference | `error_set.hpp:785-800` (annotated `HANDLED`, checked membership and handler shape); non-fixpoint grade formula `:669-694` | `error_set.test.cpp:380-405` (deduced narrowing), `:515-536` (hand-verified negatives, see C-2); `accumulating_object.test.cpp:360-420` (annotate-and-check at a fold boundary) |
| grade-generality | `grade.hpp` (framework header names no error vocabulary in code; `error_set` appears only in two doc comments); model registration confined to `error_set.hpp:836-928` | `laws.hpp` includes only `grade.hpp`, never names `error_set`/`recover`/`expected`; both models pass (`laws.test.cpp:61,321`); repo-wide grep confirms no `error_set` utterance in framework code |
| traverse-policy-surface | `traverse.hpp:145-175` (trailing defaulted value parameter, `applicative_object_for` concept, no tag types) | `accumulating_object.test.cpp:221-240` (stray third argument rejected, positive controls so it cannot pass vacuously) |
| plain-error-grade-reading | `error_set.hpp:885-893` (`grade_of<expected<T,E>>` = `error_set<E>`) | `grade.test.cpp:109-122`; `laws.test.cpp:354-369` (`grade_of` + `grade_join_t` predicts the bare-mix deduction) |
| grade-model-identity | `grade.hpp:70-72,141-142` (`grade_model`, public); tag `error_set_model` `error_set.hpp:854-859`; join-fold/lift helpers kept in `detail` `grade.hpp:144-210` | `laws.hpp:161-163` (grade and bottom share a model), `:205-207` (one sample, one model); cross-model negative `laws.test.cpp:390` |
| expected-instance-introduction | `expected.hpp:135-169,499-521` (one pinned `E` per instance object; ungraded cores unchanged in deduction) | `baseline_deduction.test.cpp` expected sections; history: registered ungraded at `1946186`, before any grade machinery (`d746b2f`) |
| grade-operation-spelling | `grade.hpp:57-81` (`grade_join`/`grade_bottom`/`grade_subsumes` + coercion `grade_subsume:227-238`); monadic `join` untouched `monad.hpp:197-201` | `grade.test.cpp:66-80` (shipped model reached through framework verbs only). See D-5 for the predicate/coercion split's logging |
| accumulation-evidence | `error_set.hpp:232-265,397-422,447` (per-type optional slots, non-empty witnessed subset, left-biased `combined_with`) | `error_set.test.cpp:238-316` (union, left bias per type, equality, associativity), `:339-361` (`witness_count`) |
| multi-witness-elimination | `visit` partial + checked `error_set.hpp:377-380,426-445`; `recover`'s fold uses only the public API `:696-755`; no public multi-witness verb exists (grep) | `error_set.test.cpp:328-346` (consteval-clean singleton visit, `witness_count` as the check-don't-trip idiom); `accumulating_object.test.cpp:287-327` (consumer story) |
| golden-vs-scheduled-assertions | Split executed at `07f4e26`/`e035a74`; `current_state.test.cpp` retired at `8cfc2d3` | The golden file itself plus the plan's Stage-5 tripwire text. See A-2 |
| bottom-grade-identity | `unit_grade` fails `grade_semilattice` (no `grade_model`/verbs registered); no `rebind_grade` at `unit_grade` exists; sentinel-lift only inside model-dispatched joins `grade.hpp:161-173` | `grade.test.cpp:50` (`!grade_semilattice<unit_grade>`); `laws.hpp:203-204` (one model, one bottom), `:249-255` (round-trip carve-out at the bottom) |
| mixing-point-vocabulary | `grade.hpp:188-196` (`mixed_grade_t`/`mixed_result_t` = lift, `grade_join_all_t`, `rebind_grade`), consumed by every graded core in `expected.hpp` (`:232,421,542`) | `laws.test.cpp:344-381` (deduced grade equals `grade_join_t` of `grade_of`s for both the graded and the bare mix, and the Boolean model drives a real mixed deduction); no parallel trait exists (grep: `mixing_grade` absent) |
| cross-model-mixing | `grade.hpp:175-192` (`mixes_with_model` on the graded cores) | `laws.test.cpp:383-390` — but only through the test-only Boolean instance. **Violated on the bare path: see A-1**, sensor gap C-1 |

Audit points 1, 2, 5 (minimal instance), 8, and 9 of the brief were checked
explicitly and are clean except where a finding below says otherwise: no
duplicate bottom machinery and no materialized framework bottom exists;
exactly one grade-reading trait exists; the minimal registration
(`crtp_absorption.test.cpp:66-92`) is two functions with zero grade
awareness and flows through `traverse`; the harness probes are as specified
(three std error enums; `int`/`optional`/`unique_ptr`, consteval-clean) and
the Boolean model both passes the full battery and drives a mixed
deduction; `laws.hpp` is reachable from the `laws` test target only and no
concept or requires-clause anywhere invokes `check_graded_laws`.

## Class A — violations

**A-1. The same-error-plus-bare cores accept a graded carrier from a
foreign model as a "bare" operand, making cross-model mixing well-formed.**
Slug: [cross-model-mixing](../decisions.md#cross-model-mixing), with
[bottom-grade-identity](../decisions.md#bottom-grade-identity) implicated
(only *ungraded* operands may lift to the model bottom; an operand with a
model grade is not ungraded).

Evidence: `detail::declares_or_bare_v` (`expected.hpp:97-104`) classifies an
operand as "bare" by `!is_expected_v` — structurally — without consulting
`grade_of`. The graded cores' `mixes_with_model` constraint is therefore
never reached for such an operand. Verified by compile probe (clang-18,
shipped headers only): register a minimal second model with carrier
`Fallible<int, may_fail>` (as `laws.test.cpp` does), then

```c++
auto f(int, const Fallible<int, may_fail> &) -> int;
applicative_typeclass<std::expected<int, std::errc>>.invoke(
    f, exp_int{1}, fallible);   // compiles; deduces expected<int, errc>
```

Two graded operands from different models combine at a mixing point, the
foreign operand's grade (`may_fail`) leaves no trace in the deduction, and
its failure state is never consulted — the framework's own `grade_of` says
this operand is graded, and the deduction treats it as a datum anyway. This
is exactly the datum-vs-grade ambiguity
[error-set-identity](../decisions.md#error-set-identity) dissolves for the
shipped model's own type, left unresolved for every other model's carriers.
The test-only Boolean instance does not have the hole (its single core
constrains *all* operands by `mixes_with_model`, `laws.test.cpp:271-274`);
only the shipped `expected` instances do — both the short-circuit and the
accumulating one (`expected.hpp:175-179, 374-378`).

Mitigation: reachable only when the user's function accepts the foreign
carrier as a parameter, and only through instances that have a bare core.
Still a hole in a constraint two Steve rulings say must reject, and it is
newly-claimed (previously-ill-formed) territory no slug licenses for datum
use. Proposed log entry, under `cross-model-mixing`:

> - 2026-08-30 — DIVERGENCE, found by the design-fidelity review. *Decision
>   says:* cross-model mixing is ill-formed by constraint. *Reality:* the
>   same-error-plus-bare cores classify operands by `is_expected_v`, so a
>   graded carrier of a foreign model passes as a bare datum
>   (`expected.hpp:97-104`); its grade and failure state vanish from the
>   deduction. *Proposed resolution:* `declares_or_bare_v`'s bare arm should
>   require the operand to be ungraded per `grade_of` (the sentinel), so a
>   foreign-model carrier falls through to the graded core and fails
>   `mixes_with_model`; add a negative sensor through the shipped `expected`
>   instance (see the review's C-1).

**A-2. The golden file was edited in the commit of the stage it gates.**
Slug: [golden-vs-scheduled-assertions](../decisions.md#golden-vs-scheduled-assertions)
and Stage 5's tripwire ("any golden test changes → STOP. … The goldens are
`baseline_deduction.test.cpp`, in full").

Evidence: commit `8cfc2d3` (stage graded-deduction) modifies
`baseline_deduction.test.cpp` (+82/−23) and deletes
`current_state.test.cpp`, in the same commit that lands the stage's code.

Assessment, both ways: the diff was examined assertion by assertion — no
existing assertion in sections 1–8 was modified, weakened, or removed; the
edit is a header-comment rewrite, one added `#include`, and an appended
section 9 promoting the retired scheduled block to its positive form. The
sensor was not inverted, and retiring `current_state.test.cpp` at its named
expiry is what the decision licenses ("visibly droppable"). But the letter
of the decision makes any `baseline_deduction.test.cpp` edit a stop-and-ask,
the commit's own "Stage tripwire clear: no existing golden changed" is an
interpretive reading of a tripwire that says "any golden test changes", and
the six new goldens of section 9 were born in the same commit as the
behavior they gate, so they never existed red against it. No stop, ask, or
ruling is logged. Proposed log entry, under `golden-vs-scheduled-assertions`:

> - 2026-08-30 — DIVERGENCE, found by the design-fidelity review. Stage
>   graded-deduction (`8cfc2d3`) edited `baseline_deduction.test.cpp` in the
>   stage commit: comment header rewritten, retired scheduled block promoted
>   into the file as new golden section 9. No existing assertion changed, so
>   the sensor was not inverted; but the tripwire's letter fired with no
>   logged stop. *Needs a ruling:* either license this shape retroactively —
>   "a stage may append its scheduled block's positive form to the golden
>   file at expiry, never touching existing assertions" — or require
>   promoted assertions to land in a separate commit (or file) so the golden
>   file's history stays edit-free at stage commits.

## Class B — undocumented decisions

**B-1. `combine_errors` and `is_error_set_of_v`: public vocabulary with no
slug and, since Stage 9, no callers.** `error_set.hpp:454-458, 532-553`.
Stage accumulating-object (`8d4b66f`) introduced public `combine_errors` as
the accumulating object's fold step; stage model-dispatched-mixing
(`e955c62`) rewired that fold through `detail::combine_grade_evidence`,
leaving both public names orphaned — `combine_errors`'s doc comment still
claims "this is the uniform step the accumulating applicative object folds
with", which is no longer true. The logged precedent is that public
vocabulary is "a decision with a slug"; these have neither slug nor caller.
Draft entry:

> ## evidence-combine-surface
>
> **Question:** What is the public surface, if any, for value-level
> evidence combination — and did `combine_errors` / `is_error_set_of_v`
> survive the model-dispatched-mixing repair as intended vocabulary or as
> residue?
> **Status:** OPEN
> **Log:**
> - 2026-08-30 — Raised by the design-fidelity review. `error_set_combine`
>   is model-native API under
>   [accumulation-evidence](#accumulation-evidence) ("`error_set` supplies
>   the semigroup itself") and has test clients. But generic
>   `combine_errors` (and its supporting trait `is_error_set_of_v`) became
>   caller-less when stage model-dispatched-mixing moved the accumulating
>   fold onto `detail::combine_grade_evidence`, and its comment still
>   describes the old role. Options: delete both as Stage-9 residue; or
>   keep them as deliberate public API and say for whom.

**B-2. `graded_context`: a public framework concept whose stated role the
framework does not give it.** `grade.hpp:130-137`. Its comment says "The
framework uses this to keep graded and ungraded paths mutually exclusive BY
CONSTRAINT, per grading-footprint" — but no shipped header uses it; the
exclusivity actually implemented is the instances' structural
declared-error matching (`all_declare_v` and complements), and the concept's
only clients are tests. This is the same shape as the Stage-8
"`grade_join_t` has no callers" finding: a public name asserted to be
load-bearing that nothing consumes. Either it is the public spelling of
grading-footprint's constraint (in which case the mechanism drifted away
from it and the decision's "(structural presence of `error_set`)"
parenthetical — see D-3 — should be re-anchored to it), or it is unslugged
public vocabulary. Draft entry:

> ## graded-context-role
>
> **Question:** Is `graded_context` the public spelling of
> [grading-footprint](#grading-footprint)'s graded/ungraded exclusivity
> constraint, or test-support that leaked into the shipped surface?
> **Status:** OPEN
> **Log:**
> - 2026-08-30 — Raised by the design-fidelity review. The concept is
>   public in `grade.hpp` and its comment claims the framework uses it for
>   mutual exclusivity; no shipped code does — the implemented exclusivity
>   is per-instance structural matching of declared error types. Note the
>   two also disagree at the margin: `graded_context<expected<T,E>>` is
>   true (semantic, post-[plain-error-grade-reading](#plain-error-grade-reading))
>   while the unmixed-`E` case runs the "ungraded" core (spelling), so
>   which one "the" constraint is has real content.

## Class C — sensor gaps

**C-1.** Cross-model rejection has no sensor through the shipped `expected`
instance. The only negative (`laws.test.cpp:390`) goes through the
test-only Boolean instance's own constraint — which is exactly why A-1 is
invisible to the suite. A `!requires` probe of
`applicative_typeclass<expected<int,errc>>.invoke` with a `Fallible`
operand (using a function that would accept it) would have caught A-1 and
pins the fix. Slug: `cross-model-mixing`.

**C-2.** Two decided compile-error behaviors are hand-verified and
documented rather than encoded: the accumulating object's refused bind with
its value-flow diagnostic (`accumulating_object.test.cpp:242-261`) and
`recover`'s two CHECKED negatives (`error_set.test.cpp:515-531`). The
documentation is honest and the repo has no negative-compile harness, so
this is the established pattern, not an oversight — but these sensors decay
silently if the diagnostics regress. Low severity; a build-system
expected-failure target would pin them. Slugs: `applicative-objects`,
`recover-grade-inference`.

**C-3.** Two Stage-9 acceptance properties are grep-shaped and inherently
unpinned: "no parallel grade-reading trait exists" and "join-fold/lift
helpers stay in `detail`". Nothing can assert an absence; noted for
completeness only, one line each in the next review.

## Class D — log drift

**D-1.** Plan §6 still lists `traverse-policy-surface` among the open
questions; it was DECIDED 2026-08-29. `transpose-grading-plan.md:399-402`.

**D-2.** `grading-footprint`'s 2026-08-28 DIVERGENCE entry still reads
"awaiting resolution"; its proposed resolution was executed and the closure
was logged only under `expected-instance-introduction` ("Divergence closed;
work resumed"). A one-line closing entry under `grading-footprint` is
missing. `decisions.md:71-87`.

**D-3.** `grading-footprint`'s decision text still says the graded/ungraded
exclusivity constraint is "(structural presence of `error_set`)". After
`plain-error-grade-reading`, the semantic trait grades plain-error
expecteds too, and the implemented constraint is declared-error structural
matching — the parenthetical describes neither. The entry was never amended
when `plain-error-grade-reading` landed (which amended
`grade-machinery-home` and `expected-instance-introduction` but not this
one). Interacts with B-2.

**D-4.** `grade-machinery-home`'s decision text still says "The CRTP base
absorbs promotion of bare values at model bottoms … as constrained
members". After the Stage-9 sentinel ruling, what the CRTP base carries is
`subsume` (promotion-as-subsumption, per crtp-absorption's logged-in-commit
insight); mixing-point promotion of bare *operands* lives in the model
instances' bare cores plus `detail::grade_lifted_into_model`, per
`bottom-grade-identity`'s "implementation helpers lift the sentinel …
inside model-dispatched joins". The 2026-08-30 amendment updated the trait
story but left this sentence unqualified. The code follows the later
ruling; the earlier sentence is what drifted.

**D-5.** Convention says amended DECIDED entries carry `Decided by:`;
`error-set-identity` (amended twice 2026-08-29) and
`expected-instance-introduction` (amended 2026-08-30) have none. Also the
`grade_subsume` → `grade_subsumes` predicate/coercion split is recorded
only in commit `bcd60f3`'s message; `grade-operation-spelling` still names
only `grade_subsume` while `grade-model-identity`'s text says
`grade_subsumes` — both names exist in code with distinct meanings, and no
entry says so.

## Verdict on the documents

The documents were sufficient to conduct this review, and notably so: every
embodiment in the table was findable from a slug's own text, the staged
history in the log matched the commit history, and the two systemic
findings (A-1, B-1/B-2) were findable *because* the log states its
invariants sharply enough to check code against — the Stage-8 entries'
"grade_join_t has no callers" pattern is what made the caller-less-public-
vocabulary and constraint-never-consulted checks obvious moves. What the
next executing agent needs added: (1) a ruling on A-2's shape, since the
next stage that retires scheduled assertions will face the same question;
(2) the D-3/D-4 sentence-level amendments, because both stale sentences
describe superseded mechanisms in one-way-door entries and a fresh agent
taking them literally would re-implement the wrong thing; (3) a statement
of where bare-operand handling belongs (instance cores vs. CRTP base), which
is currently inferable only from three entries read together. Nothing about
the review required information outside the two documents plus the repo.
