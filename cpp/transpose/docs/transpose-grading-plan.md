# Grading in beman.transpose — Contextful Evolution Plan

Status: DRAFT for review by Steve before any execution
Audience: a Claude Code agent executing concrete work in `beman.transpose`
(P3200), with follow-on guidance for `tree_algorithms`. This document is the
contract between the plan and the agent: **the Why sections are load-bearing.**

Companion: [decisions.md](decisions.md) — the decision log. Every design
decision and open question has a **slug named for the question it answers**
(never for the chosen answer, so slugs survive reversal), and every reference
to one is a link into that log. Stages carry outline numbers *and* slugs;
cross-reference stages by slug, since numbers shift when stages split.

## 0. How to use this document (divergence protocol) {#divergence-protocol}

Every stage lists Deliverables, Acceptance, and Tripwires. The rules:

1. **If reality contradicts a Why, STOP and ask.** A "why" being false means
   the design premise moved; adapting silently would produce a
   coherent-looking wrong thing.
2. **If reality contradicts a What but the Why still holds**, propose an
   adaptation in a short note and wait for approval; do not proceed on the
   original text.
3. Record every divergence as a dated Log entry under the implicated
   question's slug in [decisions.md](decisions.md): what the plan said, what
   reality is, proposed resolution. A divergence with no obviously implicated
   slug means a question nobody has asked yet — add a new OPEN section for it
   (slug the question) and log there.
4. Never "fix" a tripwire condition to make it pass. Tripwires are sensors,
   not obstacles.
5. This document is not self-updating. When a divergence is resolved, the
   resolution updates the decision log (and this plan where it repeats the
   substance), by Steve or with approval; then work resumes.

## 1. Context: what this library is and what grading is doing in it {#context}

`beman.transpose` (P3200 "Transpose") provides shape-preserving traverse:
distribute a context (expected/optional-like) out of a structure without
changing the structure's shape. Typeclass instances are non-intrusive,
registered via CRTP-produced typeclass objects pinned as NTTPs; operations
deduce their return types. Duck typing at use sites is a feature to preserve:
a gadget participates because it has the right members, not because it
declared allegiance.

**Grading** adds a compile-time index ("grade") to effectful computations:
here, the set of error types a computation may raise.
`expected<T, error_set<A,B>>` is the carrier at grade {A,B}. Grade
arithmetic:

- Algebra: finite sets of types under union. Bounded join-semilattice:
  `join = ∪`, `bottom = ∅`, order `⊆` defined by `e ⊆ f ⟺ e ∪ f = f`.
- Sequencing/combining computations joins grades. Subsumption (using a
  computation at a wider grade) is coercion along `⊆`.
- Normalization: `error_set<Es...>` is canonicalized (sorted, deduplicated)
  via type ordering (P2830; interim pretty-function fallback with documented
  restrictions: named types, external linkage, stable spelling).

**Why a semilattice and only a semilattice** — the full argument lives at
[grade-generality](decisions.md#grade-generality); the short form every stage
should keep in view: *commutative* ⇒ grade arithmetic is order-free;
*idempotent* ⇒ fold grades are shape-independent, so recursive data types
stay ungraded while effects are graded; *order-from-join* ⇒ subsumption
coercions are canonical, hence coherently implicit. Non-idempotent grades
(fuel, cost) are excluded on purpose and travel a perpendicular axis.

**WG21 posture.** Graded-monad language belongs in design rationale, never in
wording. The user-visible normative claim: error types are deduced, compose
by set union, and subsumption is implicit and coherent.

## 2. Standing decisions {#standing-decisions}

The one-way doors, catalogued with full Decision/Why/Log in
[decisions.md](decisions.md). Cheap to revisit only while Steve is the sole
client. The agent should know their one-line forms cold:

- [empty-grade-spelling](decisions.md#empty-grade-spelling) — the ∅ grade is
  bare `T`; the uniform degenerate-expected form is explicit-only.
- [grading-footprint](decisions.md#grading-footprint) — grading claims only
  previously-ill-formed territory; lazy join, no spontaneous singletons;
  graded/ungraded overloads mutually exclusive by constraint.
- [error-set-identity](decisions.md#error-set-identity) — `error_set` is
  nominal; ⊆-only conversions; impoverished as data.
- [grade-machinery-home](decisions.md#grade-machinery-home) — traits and
  grade-algebra operations live in the framework, never on the typeclass
  surface; ungraded instances work verbatim as uniformly ∅-graded.
- [applicative-objects](decisions.md#applicative-objects) — two NTTP-pinned
  applicative objects; bind only on the short-circuit one; traverse policy
  explicit; left-to-right order normative.
- [recover-grade-inference](decisions.md#recover-grade-inference) —
  recover-narrowed grades are annotated and checked, not inferred.
- [grade-generality](decisions.md#grade-generality) — `error_set` is one model
  of a `grade_semilattice` concept; non-idempotent grades excluded.
- [plain-error-grade-reading](decisions.md#plain-error-grade-reading) —
  `grade_of<std::expected<T, E>>` reports the singleton model grade
  `error_set<E>`; lazy join constrains deduced carrier spelling, not semantic
  grade reading.
- [grade-model-identity](decisions.md#grade-model-identity) — `grade_model<G>`
  maps each model grade to a nominal model tag for same-model constraints.
- [bottom-grade-identity](decisions.md#bottom-grade-identity) — framework ∅ is
  a pure ungraded sentinel; bottoms and carrier machinery exist only per
  model.
- [mixing-point-vocabulary](decisions.md#mixing-point-vocabulary) — mixing
  points dispatch through the operands' grade model via `grade_join`, not
  error-set vocabulary.
- [cross-model-mixing](decisions.md#cross-model-mixing) — graded operands at a
  mixing point must belong to the same grade model; cross-model mixing is
  ill-formed by constraint.
- [expected-instance-introduction](decisions.md#expected-instance-introduction)
  — `expected` is registered ungraded first, one pinned error type per
  instance object, before any grade machinery reaches it.
- [grade-operation-spelling](decisions.md#grade-operation-spelling) — the
  grade algebra is spelled `grade_join` / `grade_bottom` /
  `grade_subsumes`, with carrier coercion spelled `grade_subsume`;
  unqualified `join` remains the monadic join.

## 3. Work plan — beman.transpose {#work-plan}

### Stage 0 — [baseline-capture](#baseline-capture) {#baseline-capture}
Do this before touching anything.
Deliverables:
- Golden deduction tests: for a representative matrix of current inputs
  (pure values, unmixed `expected<T,E>`, `optional<T>`, containers thereof,
  through traverse and the combinators), `static_assert` the exact deduced
  result types as they are today.
- Vocabulary audit: grep the public surface; classify every mention of error
  machinery as grade-vocabulary (framework) or error-vocabulary (model),
  per [grade-generality](decisions.md#grade-generality).
Why: the golden tests are the mechanical form of
[grading-footprint](decisions.md#grading-footprint) — later stages prove
compatibility by keeping them green, not by argument.
Acceptance: tests pass against unmodified HEAD; audit note committed.
Tripwire: if current behavior already violates a standing decision (e.g.
something already normalizes eagerly), STOP — the plan assumed a baseline
that isn't there.

### Stage 1 — [expected-instance](#expected-instance) {#expected-instance}
Added 2026-08-28 by
[expected-instance-introduction](decisions.md#expected-instance-introduction);
stage numbers below shifted by one, slugs unchanged.
Deliverables: `std::expected<T,E>` registered as an ordinary Applicative and
Monad instance, ungraded, with ONE pinned error type per instance object —
`invoke` accepts operands sharing that `E`, so mixing `E1` with `E2` stays
ill-formed. Golden matrix extended with the resulting deductions, and with
negative tests pinning the mixed case as still ill-formed.
Why: this is the before-state the compatibility claim needs. Without it, the
no-spontaneous-singletons corollary of
[grading-footprint](decisions.md#grading-footprint) is an assertion about a
type that never existed; with it, stage [graded-deduction](#graded-deduction)
has something to preserve and the goldens can sense a regression. Holding
mixed `E` ill-formed here is what keeps the previously-ill-formed territory
closed until graded-deduction opens it on purpose.
Acceptance: stage [baseline-capture](#baseline-capture) goldens still green;
new goldens deduce `expected<T,E>` for unmixed pipelines with no `error_set`
anywhere; mixed-`E` combinations fail to compile (negative tests).
Tripwire: any deduced result mentioning `error_set` at this stage → STOP;
nothing in this stage may reference the grade machinery, which does not exist
yet.

### Stage 2 — [error-set-type](#error-set-type) {#error-set-type}
Deliverables: `error_set<Es...>` per
[error-set-identity](decisions.md#error-set-identity): invariant-enforcing
construction (sorted/deduped by type ordering); semilattice ops as native
API; ⊆-only converting constructors; visitation + membership for `recover`;
impoverished otherwise. Unit tests for normalization and join/bottom/subsume
laws on concrete sets.
Why: everything downstream pattern-matches this type; its invariants carry
the coherence argument (order-from-join, names-not-positions).
Acceptance: laws hold in consteval on hand-picked sets; conversions compile
exactly for subsets and fail to compile otherwise (negative tests).
Tripwires: normalization requiring type ordering on types outside the
documented fallback restrictions → STOP (P2830 dependency risk). Any
non-subset conversion compiling → STOP.

### Stage 3 — [grade-concept](#grade-concept) {#grade-concept}
Deliverables: `grade_semilattice` concept; `grade_of`, `rebind_grade`,
`subsume` with structural defaults per
[grade-machinery-home](decisions.md#grade-machinery-home); `error_set`
registered as the model.
Why: the traits are where "grading is additive" is implemented — the ∅
default for unrecognized types IS the backward-compatibility mechanism.
Acceptance: `grade_of` on every [baseline-capture](#baseline-capture) matrix
type yields ∅ except genuine carriers; goldens still green.
Tripwire: any matrix type classified as graded that today flows through the
identity path → STOP. This is the datum-vs-grade hazard;
[error-set-identity](decisions.md#error-set-identity) should have prevented
it — if it didn't, the nominal fence has a hole. See also
[datum-entry-point](decisions.md#datum-entry-point).

### Stage 4 — [crtp-absorption](#crtp-absorption) {#crtp-absorption}
Deliverables: promotion of bare values at ∅, ap-from-bind, defaulted subsume
in the CRTP base; constrained to SFINAE away cleanly.
Why: the ergonomics invariant of
[grade-machinery-home](decisions.md#grade-machinery-home) — existing
registrations must compile verbatim.
Acceptance: all existing typeclass instances build unchanged; a deliberately
minimal test instance (the "couple of functions" registration) works with
zero grade awareness.
Tripwire: any existing instance needs edits to compile → STOP.

### Stage 5 — [graded-deduction](#graded-deduction) {#graded-deduction}
Deliverables: traverse/combinators deduce joined grades at genuine mixing
points; lazy join per [grading-footprint](decisions.md#grading-footprint);
graded/ungraded paths mutually exclusive by constraint.
Why: this is the stage where previously-ill-formed mixes become well-formed;
it must be the ONLY behavioral change.
Acceptance: [baseline-capture](#baseline-capture) goldens green; new tests:
`expected<T,E1>` × `expected<T,E2>` deduces `expected<T, error_set<E1,E2>>`;
unmixed pipelines never produce `error_set`; bare/graded mixing promotes the
bare side at ∅ inside the framework only.
Tripwire: any golden test changes → STOP. Do not update a golden to make a
stage pass; that inverts the sensor. The goldens are
`baseline_deduction.test.cpp`, in full. `current_state.test.cpp` is NOT
golden — it records what the library does at a point the plan intends to
move, names this stage as the expiry, and is meant to be edited here; see
[golden-vs-scheduled-assertions](decisions.md#golden-vs-scheduled-assertions).
Its mixing-frontier block is already known to go red when flipped to the
positive form, which is the failure this stage turns green.

### Stage 6 — [accumulating-object](#accumulating-object) {#accumulating-object}
Deliverables: separate NTTP-pinned accumulating applicative object; traverse
policy parameter defaulted to the monad-derived object
(surface per [traverse-policy-surface](decisions.md#traverse-policy-surface));
static rejection of bind on the accumulating object; normative left-to-right
order documented and tested with order-observing probe effects.
Why: [applicative-objects](decisions.md#applicative-objects).
Read [accumulation-evidence](decisions.md#accumulation-evidence) BEFORE
starting: it answers what carries multiple witnesses at the value level, which
this stage's text originally left unspecified, and it amends
[error-set-identity](decisions.md#error-set-identity) — the `error_set`
shipped by [error-set-type](#error-set-type) holds one alternative and must be
revised to the witnessed-subset form first.
Acceptance: accumulating traverse collects all errors at the joined grade;
attempting bind on it is a clear compile error whose message names the
value-flow reason.

### Stage 7 — [recover-narrowing](#recover-narrowing) {#recover-narrowing}
Deliverables: `recover` with set-difference grade; annotated-and-checked
grade at fold boundaries per
[recover-grade-inference](decisions.md#recover-grade-inference).
Read [multi-witness-elimination](decisions.md#multi-witness-elimination)
BEFORE starting: it settles how a multi-witness value is eliminated, and the
answer is that `recover` needs no new public verb. The handled set {H} is a
compile-time type-set, so elimination is a static fold over the grade with
runtime presence filtering — membership plus `witness<E>()`, both of which
already exist. Do not add a public multi-witness eliminator; the absence is
the fence line, not a gap.
Acceptance: narrowing verified in deduced types; a recover-inside-fold test
demonstrating the annotate-and-check path. Also cover the CONSUMER story:
accumulating traverse (stage [accumulating-object](#accumulating-object)) is
where multi-witness values first reach user hands, so the tests should show
what a caller actually does with an accumulated error — `witness_count()` and
`witness<E>()` inspection, and `recover` — so the documented story exists
before anyone asks for the verb this plan declined to ship.
Tripwire: implementation pressure to infer via lattice fixpoint → STOP and
discuss (compile-time cost vs spec complexity).

### Stage 8 — [law-harness](#law-harness) {#law-harness}
Deliverables:
- `laws.hpp` consumed only by test targets: `consteval bool
  check_graded_laws<Obj>()` usable as `static_assert(...)`.
- Grade probes: `std::errc`, `std::io_errc`, `std::future_errc` — three
  distinct named std enum types, inside the type-ordering fallback
  constraints by construction. Checking over the free semilattice on three
  generators (eight elements) exercises every law shape: unit at ∅,
  idempotence, commutativity, associativity.
- Value probes: `int`, `std::optional<int>`, `std::unique_ptr<int>`
  (move-only, constexpr since C++23 — catches stray copies), staying inside
  consteval.
- Second model: the Boolean semilattice {⊥,⊤} registered as a test-only
  model (long-term home: [optional-grade-model](decisions.md#optional-grade-model));
  full harness run against it.
Why: the harness is a test deliverable, not a registration gate — semantic
requirements stay in prose, checking stays opt-in (the standard's own
posture; a std-shipped bool-returning checker would migrate into `requires`
clauses and destroy the pay-once economics — see the deliberate-omissions
item in [paper-revision](#paper-revision)). The second model is the leak
detector per [grade-generality](decisions.md#grade-generality): every place
it fails to slide in cleanly is a framework/model leak — log a divergence,
don't patch around it.
Acceptance: harness green on both models; harness written against the
concept, instantiated with the models.

### Stage 9 — [model-dispatched-mixing](#model-dispatched-mixing) {#model-dispatched-mixing}
Deliverables:
- Make framework ∅ a pure sentinel per
  [bottom-grade-identity](decisions.md#bottom-grade-identity): `grade_of`
  yields either ungraded or a model grade, and the sentinel has no lattice
  membership or carrier machinery.
- Change plain-error expected grade reading per
  [plain-error-grade-reading](decisions.md#plain-error-grade-reading):
  `grade_of<std::expected<T, E>>` is the singleton `error_set<E>` even though
  unmixed deductions keep spelling the carrier as `std::expected<T, E>`.
- Add public model identity per
  [grade-model-identity](decisions.md#grade-model-identity): model grades
  specialize `grade_model<G>`, and same-model constraints compare those tags.
- Route every mixing-point deduction through the operands' grade model per
  [mixing-point-vocabulary](decisions.md#mixing-point-vocabulary):
  `rebind_grade<Carrier, grade_join<g1, g2>>`, with ungraded operands lifted
  to that model's bottom at the mixing point.
- Constrain graded mixing points to a single grade model per
  [cross-model-mixing](decisions.md#cross-model-mixing); cross-model mixing is
  ill-formed, and no product-of-models machinery is introduced.
- Add a Boolean-model mixed deduction that actually drives the machinery:
  `Fallible<T, may_fail>` combined with `Fallible<T, never_fails>` deduces the
  joined Boolean grade.
- Keep the existing goldens green; shipped deductions must still express
  error-specific joining only inside the `error_set` model layer.
Why: the Stage 8 law harness did its job by proving the second model can
register and pass laws while still being unable to drive a real deduction.
That is the abstraction-boundary leak [grade-generality](decisions.md#grade-generality)
was designed to detect, and paper-revision must not start while the artifact
only half demonstrates the claim.
Acceptance: Boolean mixed deduction green; cross-model mixing rejected by
constraint; baseline goldens unchanged; no parallel grade-reading trait
exists; no shipped mixing-point deduction code mentions `error_set` outside
the model layer; `make TOOLCHAIN=gcc-16 compile`,
`make TOOLCHAIN=gcc-16 ctest`, and `make TOOLCHAIN=gcc-16 compile-headers`
green.
Tripwire: needing a product of grade models, changing the golden baseline, or
weakening [grading-footprint](decisions.md#grading-footprint) to make
singleton lifting easy → STOP and ask.

### Stage 10 — [paper-revision](#paper-revision) {#paper-revision}
Deliverables: P3200 rationale sections — coherence argument (nominal
`error_set`, subset-only conversions, sorted normalization as
names-not-positions); compatibility section (three sentences: pure paths
identical per [empty-grade-spelling](decisions.md#empty-grade-spelling);
unmixed paths identical by lazy join; previously-invalid mixes now valid,
additive — plus the detection-idiom caveat); deliberate omissions with
reasons (non-idempotent grades; a std law-checker, with the
constraint-capture rationale); normative traversal order; graded-monad
language confined to rationale.
Why: deliberate omissions with recorded reasons survive review from both
directions, and plant the counterargument for future re-proposals in our
handwriting.

## 4. Guidance — tree_algorithms {#tree-algorithms}

Do not start until [error-set-type](#error-set-type) through
[graded-deduction](#graded-deduction) are stable; tree_algorithms consumes
them.

- [fold-grade-invariant](#fold-grade-invariant) — document as an invariant:
  fold grades are shape-independent iff the grade algebra is a bounded
  join-semilattice ([grade-generality](decisions.md#grade-generality)). This
  is the wall between "grows an error feature" and "needs indexed fixpoints."
  `Fix` stays ungraded; fold carriers are ordinary types instantiated at the
  join grade (`algebra_grade_t` = join of per-clause grades).
- [cata-entry-points](#cata-entry-points) — two entry points per
  [applicative-objects](decisions.md#applicative-objects): monadic cata
  (effectful algebra clauses; short-circuit only — the per-layer bind forces
  it) vs applicative cata (pure algebra, effectful layer/leaves; accumulating
  object admissible). Do not offer one entry point that silently picks.
- [widen-once](#widen-once) — compute `algebra_grade_t` up front and run the
  whole fold in the saturated fiber: inject at leaves/first raise, never
  coerce per merge node (subsumption is a retyping in theory but a
  representation change in C++).
- [recover-in-clauses](#recover-in-clauses) — recover inside algebra clauses
  breaks grade = join-of-clauses
  ([recover-grade-inference](decisions.md#recover-grade-inference) fixpoint);
  require annotation at the fold boundary.
- [fuel-axis](#fuel-axis) — fuel/sized experiments (graded unfold,
  budget-resumption across constexpr contexts) are prototyped in
  compile-time-scheme, not here; if adopted later they arrive as an NTTP axis
  on the coalgebra/driver side, perpendicular to error grading; componentwise
  product of grades if both ever coexist.

## 5. Scoping note — fingertree {#fingertree}

Recommendation: **no structural grading work in fingertree.** Reasoning to
preserve:

The Hinze–Paterson design is already graded, twice, and its choices match
this plan's theory exactly:
- The *measure annotation* is a monoid-valued grade stored as data —
  Writer-style, value-level. It must be value-level: measures (sizes,
  priorities) are generally non-idempotent monoids, so the grade of a tree
  depends on runtime shape — precisely the case
  [grade-generality](decisions.md#grade-generality) excludes from type-level
  grading. The proven design already made the correct call.
- The *nested (non-uniform) recursion* (`Node` depth) is a static depth
  grade — polymorphic recursion is type-level grading the structure already
  performs implicitly.

So "fingertree-like with graded internal node types" would be making the
second point explicit — legitimate as an article, but re-deriving the design,
not extending it. Litmus test for any proposal there: if it changes the
measure-monoid requirements or the 2-3 digit/balance invariants, it is not a
fingertree.

Error-set grading touches fingertree only as a *client*: traversing a
fingertree with effectful functions goes through Transpose and inherits
graded traverse for free, requiring nothing beyond its existing traversable
registration.

## 6. Open questions {#open-questions}

Tracked as OPEN entries in the decision log, same namespace as decisions
(answering one graduates it in place; links never break):
[uniform-form-surface](decisions.md#uniform-form-surface),
[datum-entry-point](decisions.md#datum-entry-point),
[optional-grade-model](decisions.md#optional-grade-model).
