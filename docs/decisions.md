# Decision Log — grading in beman.transpose

Convention: each section answers one **question**, identified by a slug named
for the question, never the chosen answer (so the slug survives reversal:
`#empty-grade-spelling`, not `#bare-t`). All references anywhere in the repo
render as links to these anchors. Open questions live in the same namespace
with `Status: OPEN`; answering one graduates it in place — the slug and every
existing link stay valid. Divergences append dated entries to the implicated
question's Log; they do not get their own files.

Entry shape: Question / Status / Decision / Why / Log.
New or amended DECIDED entries also carry `Decided by` so later agents can distinguish Steve rulings from stage-local observations.

---

## empty-grade-spelling

**Question:** How is the ∅ (empty) grade spelled — bare `T` or
`expected<T, error_set<>>`?
**Status:** DECIDED 2026-08-28
**Decided by:** Planning discussion; Stage 8 generalization affirmed by Steve Downey 2026-08-30.
**Decision:** Bare `T`. The uniform degenerate-expected form remains available
as an explicit spelling with the isomorphism documented once
(see [uniform-form-surface](#uniform-form-surface)).
**Why:** Bare `T` makes the unit fiber *identical* to the ungraded API, not
merely isomorphic — pure paths deduce character-for-character what they deduce
today, so grading has zero footprint until `error_set` is uttered. The
subsumption coercion out of ∅ is `expected`'s existing converting constructor
from `T`; the standard already implements η's coercion. Known deliberate
divergence from libfn, which spells the identity monad
`fn::expected<T, fn::copack<>>` (uniform family, unconstructible error
alternative) — a coherent choice for a closed pipeline library, the wrong
trade for an open boundary.
**Sentinel:** any framework path materializing `expected<T, error_set<>>`
without the user writing it violates this decision.
**Log:**
- 2026-08-28 — Adopted in planning discussion (graded monads thread).
- 2026-08-28 — Sentinel partially mechanized by stage
  [baseline-capture](transpose-grading-plan.md#baseline-capture): bare `int`
  is pinned as an *unregistered* context in the golden tests, so promotion at
  ∅ (stage [crtp-absorption](transpose-grading-plan.md#crtp-absorption))
  cannot arrive by quietly registering bare values as a carrier.
- 2026-08-30 — Sentinel generalized off the shipped model by stage [law-harness](transpose-grading-plan.md#law-harness): the harness asserts for EVERY model that re-indexing a carrier at that model's bottom yields the bare value, so "no framework path materializes an ∅-graded carrier the user did not write" is now checked for the Boolean model too, not only for `error_set`.
  Doing so surfaced that this decision's ∅ and the framework's `unit_grade` are different types that behave differently here — see [bottom-grade-identity](#bottom-grade-identity).
  Steve's ruling accepts the generalization but changes the implementation target: framework-∅ is a pure sentinel, not a model grade or carrier.

---

## grading-footprint

**Question:** What is grading permitted to change for existing clients at the
API level?
**Status:** DECIDED 2026-08-28
**Decided by:** Planning discussion; amended by Steve Downey 2026-08-30.
**Decision:** Grading claims only previously-ill-formed territory. For any
input combination that deduces a type today, the graded framework deduces the
same type. `error_set` appears in a deduced result only when an input already
carried one, or the combination was previously ill-formed (mixing
`expected<T,E1>` with `expected<T,E2>`, which now joins). Corollary — no
spontaneous singletons: unmixed `expected<T,E>` pipelines never become
`expected<T, error_set<E>>`; join is lazy, entering only at a genuine mixing
point. Graded and ungraded paths are mutually exclusive by semantic
`grade_of` / `graded_context` constraints; expected's lazy-spelling path also
requires declared-error matching, so foreign graded carriers are not treated
as bare operands.
**Why:** This is the entire additive-compatibility story, and it is available
only because of [empty-grade-spelling](#empty-grade-spelling). Accepted
residue: previously-ill-formed combinations becoming well-formed flips
detection idioms (`requires`, SFINAE) — additive and tolerated; changed
deductions on previously-valid code are not tolerated.
**Log:**
- 2026-08-28 — Adopted; mechanized as the golden deduction tests in stage
  [baseline-capture](transpose-grading-plan.md#baseline-capture).
- 2026-08-28 — DIVERGENCE, raised by
  [baseline-capture](transpose-grading-plan.md#baseline-capture). *Plan said:*
  the baseline matrix includes unmixed
  `expected<T,E>`, and the newly-well-formed territory is "mixing
  `expected<T,E1>` with `expected<T,E2>`". *Reality:* `std::expected` appears
  nowhere in the repository — not registered as an applicative, monad, or
  functor — so neither the unmixed nor the mixed case deduces anything today.
  Both are ill-formed, and for the same reason: no instance, rather than no
  join. *Assessment:* the Why is unharmed and arguably strengthened. For
  `expected` the graded framework claims entirely new territory, so additive
  compatibility there is trivially satisfied; the real compatibility burden
  falls on the optional / vector / sender / zip_list / array paths, which the
  goldens now pin. *Proposed resolution:* keep this decision as written;
  capture the baseline over the carriers that exist; pin `expected`'s
  non-registration as an explicit negative golden so a later stage flipping it
  is deliberate; and settle where the ungraded instance comes from under
  [expected-instance-introduction](#expected-instance-introduction).
- 2026-08-28 — Closed by
  [expected-instance-introduction](#expected-instance-introduction):
  `expected` was registered ungraded first, then the later grade stages
  preserved its existing same-error carrier spelling while adding only the
  previously ill-formed mixed-error territory.

---

## error-set-identity

**Question:** Is `error_set` a nominal type or any suitably normalized
structural sum?
**Status:** DECIDED 2026-08-28
**Decided by:** Planning discussion; amended by Steve Downey 2026-08-29.
**Decision:** Nominal. `error_set<Es...>` is its own type: canonicalization
(sorted, deduplicated via type ordering) is a class invariant enforced at
construction; converting constructors encode exactly the `⊆` widenings and
nothing else; the data-facing API is deliberately impoverished **but Regular**
(visitation and membership for `recover`, plus equality and copy/move; not a
variant competitor). May share storage/visit machinery with a structural sum
by composition or private inheritance; the public identity never slices into
the structural world.

**Value-level invariant (amended 2026-08-29, see
[accumulation-evidence](#accumulation-evidence)):** a value holds a *non-empty
witnessed subset* of its grade — for each raised type, at most one witness.
The type says *may raise*; the value says *did raise*, and did-raise is a
subset of may-raise. Storage is per-type slots bounded by |grade|, not a
one-of union: no allocation, constexpr-clean. Equality is "same present set,
and equal witnesses". "Impoverished" was always about not competing with
`variant` — no monostate conveniences, no assignment gymnastics — never about
irregularity.
**Why:** Type as semantics. A sum of types is representation; "the set of
errors this computation may raise" is an interpretation, and interpretations
need names. Nominality makes structural grade detection sound (it conscripts
only the willing) and dissolves the datum-vs-grade ambiguity at the
declaration site: `expected<T, variant<A,B>>` is a value-level sum error,
`expected<T, error_set<A,B>>` is the graded carrier. Having *only* the subset
conversions is the coherence argument compiled into the overload set (sorted
normalization = names-not-positions; inclusions unique). Precedents:
`chrono::duration`, `std::byte` — semantics carried by what the type refuses.
**Log:**
- 2026-08-28 — Adopted.
- 2026-08-29 — ADDITION, made by stage
  [graded-deduction](transpose-grading-plan.md#graded-deduction); flag if
  unwanted. `error_set_of` gained a defaulted `operator==`, which the
  impoverished-API list (visitation, membership) did not enumerate. *Reason:*
  `std::expected<T,E>` compares equal whenever `E` does, so without it
  `expected<T, error_set<...>>` silently loses equality and grading becomes a
  usability regression at precisely the point it claims to be additive. That
  reads as against the spirit of [grading-footprint](#grading-footprint) even
  though its letter does not apply, these types being new. *Assessment:*
  equality on a sum of comparable alternatives is not a step toward competing
  with `variant` — it exposes no alternative, no index, and no storage. It is
  defaulted, so it is deleted rather than ill-formed when an alternative is
  not comparable.
- 2026-08-29 — Ruling (Steve): keep the `operator==`, and amend the decision
  rather than the code. "Impoverished" meant not a variant competitor — no
  monostate conveniences, no assignment gymnastics — not irregular. Regularity
  is table stakes and was already half-present via copy/move. Decision text
  above now reads "impoverished but Regular".
- 2026-08-29 — AMENDMENT at the value level, from
  [accumulation-evidence](#accumulation-evidence): the invariant moves from
  "exactly one alternative" to "at least one", storage from a one-of union to
  per-type slots, and equality to "same present set, equal witnesses". Note
  for whoever reads this slug next: this is the second amendment to it in a
  week, and both times the cause was the same — value semantics left
  underspecified relative to type semantics. Worth suspecting that pattern
  anywhere else the log states a type-level rule without saying what the
  values do.
- 2026-08-29 — `visit` is now PARTIAL, and checked. The witnessed-subset
  amendment made it possible to hold more than one witness, which left `visit`
  with a documented but unenforced precondition and a `to_variant` that
  silently returned the leftmost witness — a dropped error surfacing far from
  its cause. Violation is now a compile error in a constant expression
  (`to_variant` calls a non-constexpr function on that path) and stops the
  program at runtime. `witness_count()` is public so a caller can check rather
  than trip: an unenforceable contract callers cannot inspect is a trap, not a
  contract. Note this is a real narrowing of the surface — `visit` was total
  before the amendment, and `error-set-identity` lists visitation as one of
  the two things the API does offer — so the multi-witness case now has no
  visitation verb at all, only per-type `witness<E>()`. If
  [recover-narrowing](transpose-grading-plan.md#recover-narrowing) wants one,
  that is a question for a new slug rather than an addition to this one.

---

## grade-machinery-home

**Question:** Where does grade machinery live — typeclass surface, or
framework/grade-algebra infrastructure?
**Status:** DECIDED 2026-08-28
**Decided by:** Planning discussion; Stage 9 amendments by Steve Downey 2026-08-30.
**Decision:** Never on the typeclass surface. `grade_of<Ctx>` and
`rebind_grade<Ctx,G>` are framework traits: `grade_of` defaults unregistered
carriers to the ungraded sentinel, and models specialize registered carriers
to model grades. `join`/`bottom`/`subsume` are operations of the grade algebra
(`grade_semilattice` concept), written once, with `error_set` as the shipped
model. Plain-error `std::expected<T, E>` is semantically graded at
`error_set<E>` per [plain-error-grade-reading](#plain-error-grade-reading);
lazy join remains a carrier-spelling rule, not a second grade trait. The CRTP
base carries ap-from-bind and the defaulted `grade_subsume` coercion as
constrained members that SFINAE away silently. Mixing-point bare-operand
lifting lives in the model-dispatched deduction helpers, where an ungraded
operand is lifted to the current model's bottom.
**Why:** Gadget-author ergonomics: registering a kind must stay "a couple of
functions," and duck typing at use sites is a feature to preserve. Invariant:
an instance that knows nothing about grades works verbatim, treated as
uniformly ∅-graded; the monad instance remains *identical to* the applicative
instance because grades ride in deduced return types — there is no separate
graded spelling to diverge into.
**Sentinel:** a typeclass instance that must declare grade participation, or a
second grade-reading trait beside `grade_of`, means the factoring has leaked.
**Log:**
- 2026-08-28 — Adopted.
- 2026-08-28 — Spelling snag found by
  [baseline-capture](transpose-grading-plan.md#baseline-capture): `join` in
  this library already means monadic join. Deferred to
  [grade-operation-spelling](#grade-operation-spelling); does not disturb the
  decision, which is about where the operations live, not what they are
  called.
- 2026-08-30 — Amended by [plain-error-grade-reading](#plain-error-grade-reading) and [grade-model-identity](#grade-model-identity).
  The framework still owns the traits, but the ungraded sentinel is no longer a grade and registered carriers report model grades through the single `grade_of` question.

---

## applicative-objects

**Question:** How do the two applicative structures over one carrier
(short-circuit, accumulating) relate, and which owns bind?
**Status:** DECIDED 2026-08-28
**Decision:** Two distinct NTTP-pinned typeclass objects over the same carrier
and grade algebra. Bind belongs to the short-circuit (monad-derived) object
only; the framework never auto-derives bind for the accumulating object.
Traverse takes an explicit, defaulted applicative-object policy
(see [traverse-policy-surface](#traverse-policy-surface)). Traversal order is
specified normatively: left-to-right.
**Why:** Accumulation has no graded bind — when the first computation failed
there is no value to feed the continuation, so the promised joined grade
cannot be honored; a value-flow obstruction no grade bookkeeping fixes.
Normative order is required because grades are order-blind (∪ commutes) while
short-circuit *values* are order-sensitive (which error is observed first
depends on child order) — the types cannot pin what the wording must.
**Log:**
- 2026-08-28 — Adopted.

---

## recover-grade-inference

**Question:** Are grades narrowed by `recover` inferred or annotated at fold
boundaries?
**Status:** DECIDED 2026-08-28
**Decision:** Annotated and checked. `recover` handling {H} takes grade e to
(e ∖ H) ∪ raised; inside recursive folds, inference of the resulting grade is
a least-fixed-point computation on the lattice. The user annotates the
intended grade; the framework verifies. Inference only where no fixpoint is
required.
**Why:** The fixpoint is finite (bounded lattice) but runs as template
recursion — compile-time cost and specification complexity for a rare
construct. Annotate-and-check keeps grade computation a fold of joins.
**Log:**
- 2026-08-28 — Adopted.

---

## grade-generality

**Question:** How general is the grade algebra — is `error_set` the grade, or
one model of a grade concept?
**Status:** DECIDED 2026-08-28
**Decision:** One model of a concept. The framework layer speaks only grade
vocabulary (`grade_of`, `join`, `subsume`, `bottom`); error vocabulary
(`error_set`, `recover`, ⊆-as-may-raise) is confined to the model layer. A
future algebra is adopted by supplying a `grade_semilattice` model with
decidable type-level canonical forms. Deliberately excluded: non-idempotent
grade monoids (cost, fuel) — fold grades would become runtime-shape-dependent,
forcing indexed data types; fuel is a perpendicular NTTP axis prototyped in
compile-time-scheme, entering (if ever) as a componentwise product of grades,
never through the error door.
**Why:** The three semilattice properties are load-bearing everywhere:
commutative ⇒ order-free grade arithmetic; idempotent ⇒ shape-independent
fold grades (Fix stays ungraded); order-from-join ⇒ canonical, coherent
subsumption. The concept-with-one-shipped-model posture is kept honest by a
second test-only model (see [optional-grade-model](#optional-grade-model) and
stage [law-harness](transpose-grading-plan.md#law-harness)): an abstraction
with one model is renamed, not generic.
**Log:**
- 2026-08-28 — Adopted.
- 2026-08-30 — LEAK-DETECTOR RESULT, from stage [law-harness](transpose-grading-plan.md#law-harness).
  The Boolean semilattice was registered as the promised second model and the full harness run against both.
  Verdict is split, and the split is exactly along the layer boundary this decision draws.
  *Upheld at the algebra and the carrier traits:* `tests/beman/transpose/laws.hpp` includes `grade.hpp` and nothing else from the library, never names `error_set`, `recover`, or `expected`, and both models pass it — so the framework layer really can state and check the semilattice laws without naming its shipped model.
  *Not upheld at the mixing point,* which is the one place the algebra exists for: `grade_join_t` has no callers in `include/` at all, and every graded deduction joins through `detail::joined_error_t` in error vocabulary.
  Filed as [mixing-point-vocabulary](#mixing-point-vocabulary), which is a contradiction of this decision's letter and needs Steve's ruling on whether it re-opens it.
  *A third finding,* smaller but structural, is that the framework and every model each carry their own ∅ and the two are never identified — [bottom-grade-identity](#bottom-grade-identity).
  Nothing was patched: this stage's charter is to log what the second model exposes, not to smooth it.
- 2026-08-30 — REPAIR, by stage [model-dispatched-mixing](transpose-grading-plan.md#model-dispatched-mixing).
  `grade_join_t` now drives expected mixing points and the Boolean model drives an actual mixed deduction, so the leak detector's positive result has been repaired rather than documented around.

---

## uniform-form-surface

**Question:** What is the surface for the explicit uniform spelling (the
documented iso from [empty-grade-spelling](#empty-grade-spelling)) —
constructor, named function, or both?
**Status:** OPEN
**Log:**
- 2026-08-28 — Raised during planning.

---

## datum-entry-point

**Question:** Is an `as_computation`-style explicit entry needed for the rare
"error_set as a datum" author, or does the
[error-set-identity](#error-set-identity) fence make it YAGNI until a
divergence proves otherwise?
**Status:** OPEN
**Log:**
- 2026-08-28 — Raised during planning; default posture is YAGNI.

---

## traverse-policy-surface

**Question:** How is the traverse applicative-object policy spelled at call
sites — NTTP object parameter or tag type?
**Status:** DECIDED 2026-08-29
**Decision:** The policy is *the existing NTTP-pinned applicative object
itself* — not a new type — passed as a **trailing defaulted value parameter**,
the shape `std::ranges` algorithms use for `comp = {}, proj = {}`. POLICY is
constrained by a concept ("is an applicative object for this carrier"). No tag
types.
The constraint is load-bearing twice over: a stray third argument — someone's
extra container — fails loudly instead of being silently swallowed as a
policy, and it is the enforcement hook at the traverse boundary for the
framework refusing bind-derivation on the accumulating object.
**Why:** An explicit template parameter (`traverse<accumulating>(f, xs)`)
would rule out ever spelling `traverse` as a CPO, since call syntax cannot
supply template arguments to `operator()` — and in a HOF-centric library
`traverse` wants to be passable to other combinators. Working around it by
making `traverse` a variable template of callables breaks the *default* call:
`traverse(f, xs)` becomes `traverse<>(f, xs)`, changing every existing call
site and failing the goldens. So the explicit-template spelling quietly
forecloses the object form; the surface decision would settle a
customization-point question nobody has asked.
The trailing defaulted parameter costs nothing to get this: the objects are
stateless, so type is identity, dispatch is type-directed and constant-folded,
and default call sites are character-identical to today. Composition comes
free — `bind_back(traverse, accumulating)` is the accumulating traverse as a
first-class object, no wrapper lambda. It is also the LEWG-friendliest
precedent to cite, being the ranges convention rather than the
`sort(par, ...)` policy-first one.
Tag types are rejected as a *shadow identity*: `accumulating_t` would be a
second name for a structure that already has a nominal one, the applicative
object itself — precisely what the NTTP-object design exists to prevent.
**Log:**
- 2026-08-28 — Raised during planning.
- 2026-08-29 — Answered: trailing defaulted constrained value parameter, on
  the ranges `comp={}, proj={}` precedent; no tag types. The deciding
  consideration was that an explicit-template spelling forecloses a CPO
  `traverse`.

---

## optional-grade-model

**Question:** Where does the Boolean semilattice model ({⊥,⊤}, the "may-fail
bit") live long-term — test-only leak detector, or shipped as `optional`'s
official grade registration?
**Status:** OPEN
**Log:**
- 2026-08-28 — Raised during planning. Note: shipping it quietly unifies
  optional and expected under one framework and likely belongs in the paper's
  rationale either way.
- 2026-08-30 — The model now EXISTS, test-only, in `tests/beman/transpose/laws.test.cpp`, built by stage [law-harness](transpose-grading-plan.md#law-harness).
  Still open, and deliberately so: the carrier is a purpose-built `Fallible<T>`, not `std::optional`, because registering `std::optional` as a graded carrier would answer this question by fiat — and would contradict `grade.test.cpp`'s `is_ungraded<std::optional<int>>`, which stage [grade-concept](transpose-grading-plan.md#grade-concept) pinned as part of its ∅-default tripwire.
  Two facts for whoever answers this.
  *The price is now measured:* the algebra is ten trivial specializations and slides in cleanly, but the carrier costs four more, all transliterations of `error_set.hpp`'s, and two of the four exist only because of [bottom-grade-identity](#bottom-grade-identity).
  *The benefit is currently unavailable:* per [mixing-point-vocabulary](#mixing-point-vocabulary) a registered algebra is not a usable one, so shipping this today would register `optional` as graded without letting it join with anything.
  Answering yes probably wants that resolved first.
- 2026-08-30 — Superseded by
  [model-dispatched-mixing](transpose-grading-plan.md#model-dispatched-mixing):
  the Boolean model now drives a real mixed deduction, so the "registered but
  not usable" objection above is closed. The question remains open because
  shipping the Boolean model as `optional`'s grade registration is a public
  surface decision, not an implementation-blocker.

---

## plain-error-grade-reading

**Question:** What grade does `grade_of<std::expected<T, E>>` report when `E` is a plain error type rather than an `error_set`?
**Status:** DECIDED 2026-08-30
**Decided by:** Steve Downey.
**Decision:** It reports the singleton model grade `error_set<E>`.
This is type-level bookkeeping only: an unmixed pipeline still deduces `std::expected<T, E>`, not `std::expected<T, error_set<E>>`.
Lazy join is a discipline on deduced carrier spellings, not on semantic grade reading.
There is no parallel grade-reading trait; consumers ask `grade_of` once.
**Why:** `std::expected<T, E>` is a registered carrier in the `error_set` family, so reporting the framework's ungraded sentinel would violate [bottom-grade-identity](#bottom-grade-identity), which says `grade_of` yields either ungraded or a model grade.
The singleton reading materializes no new runtime or deduced carrier form; it only lets the framework compute joins in grade vocabulary.
**Log:**
- 2026-08-30 — Raised by the Opus sanity check before [grade-concept](transpose-grading-plan.md#grade-concept), but not given its own slug at the time.
  The grade-concept stage pinned the opposite answer in tests by treating plain-error `expected` as ungraded.
- 2026-08-30 — Stage [model-dispatched-mixing](transpose-grading-plan.md#model-dispatched-mixing) initially tried to route around the tension with a second per-model `mixing_grade` hook.
  Steve stopped that direction: two grade-reading traits would make every consumer know which one lies.
  The repair instead changes `grade_of<std::expected<T, E>>` to the singleton semantic grade and preserves lazy spelling at deduction sites.

---

## grade-model-identity

**Question:** How does the framework know whether two grades belong to the same model?
**Status:** DECIDED 2026-08-30
**Decided by:** Steve Downey.
**Decision:** A public `grade_model<G>` trait maps every model grade to a nominal model tag.
Same-model constraints compare those tags.
The tag carries identity only: joins, bottoms, and subsumption remain operations on grades through `grade_join`, `grade_bottom`, and `grade_subsumes`.
Join-fold and sentinel-lift helpers used by implementation code stay in `detail`.
**Why:** [cross-model-mixing](#cross-model-mixing) needs a way to reject operands from different grade models without inventing a product model.
Nominal model tags are the smallest public vocabulary that expresses that constraint while keeping model operations on the existing grade algebra hooks.
**Log:**
- 2026-08-30 — Added by stage [model-dispatched-mixing](transpose-grading-plan.md#model-dispatched-mixing) under Steve's ruling.
  The aborted `mixing_grade` direction was not kept; the only new public framework hook is model identity.

---

## expected-instance-introduction

**Question:** Where does the *ungraded* `std::expected` applicative/monad
instance come from — its own stage before
[graded-deduction](transpose-grading-plan.md#graded-deduction), or does
grading introduce `expected` to this library already graded?
**Status:** DECIDED 2026-08-28
**Decided by:** Planning discussion; amended by Steve Downey 2026-08-30.
**Decision:** Ungraded first, as its own stage. `std::expected<T,E>` is
registered as an ordinary applicative and monad — one pinned error type per
instance object, so mixing `E1` with `E2` remains ill-formed until
[graded-deduction](transpose-grading-plan.md#graded-deduction) — and folded
into the golden deduction matrix before grade machinery reaches its
deductions. Placed immediately after
[baseline-capture](transpose-grading-plan.md#baseline-capture) as stage
[expected-instance](transpose-grading-plan.md#expected-instance), earlier than
the "before graded-deduction" minimum the question asked for. Amended by
[plain-error-grade-reading](#plain-error-grade-reading): once grade machinery
exists, `grade_of<std::expected<T, E>>` reports the singleton semantic grade;
the ungraded-first before-state is about carrier spelling and typeclass
registration, not the final grade trait answer.
**Why:** Without an ungraded before-state the no-spontaneous-singletons
corollary of [grading-footprint](#grading-footprint) has nothing to be true
*of*: "unmixed pipelines never become `expected<T, error_set<E>>`" would be an
assertion about a type that never existed, unfalsifiable by the goldens that
exist to falsify exactly that. Registering it before
[grade-concept](transpose-grading-plan.md#grade-concept) rather than after
also puts `expected<T,E>` into the matrix before graded deduction can change
its carrier spelling, which is the hard case the no-spontaneous-singletons
corollary needs. Keeping one error type per instance object is what holds the
previously-ill-formed territory closed until
[graded-deduction](transpose-grading-plan.md#graded-deduction) opens it
deliberately.
**Log:**
- 2026-08-28 — Raised by stage
  [baseline-capture](transpose-grading-plan.md#baseline-capture). No stage in
  the plan registers `expected` at all, graded or otherwise, yet
  [graded-deduction](transpose-grading-plan.md#graded-deduction) and
  [recover-narrowing](transpose-grading-plan.md#recover-narrowing) both assume
  the carrier is present. Two consequences worth weighing before answering.
  *First,* sequencing: only an ungraded-first introduction gives the
  no-spontaneous-singletons corollary of
  [grading-footprint](#grading-footprint) something to be true *of* — with no
  ungraded `expected<T,E>` ever in the library, "unmixed pipelines never
  become `expected<T, error_set<E>>`" has no before-state to preserve and
  degrades from a compatibility guarantee into an assertion about a type that
  never existed. *Second,* `pure`: an `expected` instance can only name an
  error type by taking it from the pinned instance object, so the ∅ grade has
  no `pure` of its own — which is exactly the bare-value promotion that stage
  [crtp-absorption](transpose-grading-plan.md#crtp-absorption) absorbs, and it
  arrives earlier than the plan's ordering suggests.
- 2026-08-28 — Answered: ungraded first, as a new stage placed directly after
  baseline-capture. Divergence closed; work resumed.
- 2026-08-30 — Amended by [plain-error-grade-reading](#plain-error-grade-reading).
  The original "ungraded first" answer remains true for the staged
  introduction and the deduced carrier spellings, but not for the final
  semantic `grade_of` reading after grade machinery is installed.

---

## grade-operation-spelling

**Question:** How are the grade-algebra operations spelled, given that `join`
in this library already means monadic join?
**Status:** DECIDED 2026-08-28
**Decided by:** Planning discussion; amended by Steve Downey 2026-08-30.
**Decision:** `grade_`-prefixed operations — `grade_join`, `grade_bottom`,
the order predicate `grade_subsumes`, and the carrier coercion
`grade_subsume`. Monadic `join` keeps its name unqualified and unchanged.
**Why:** This is the library's own established shape one level up:
`monoid_combine` and `monoid_identity` are free verbs dispatching to
`Monoid<T>`, and the grade semilattice is the same kind of object. It keeps
the free-verb surface every other operation in the library presents, keeps
lookup static and explicit per the typeclass-object invariants in
`detail/typeclass_base.hpp`, and resolves the collision without introducing a
namespace level the library does not otherwise use. The prefix also reads
correctly at the call site, where the operand is a grade and not a monad.
**Log:**
- 2026-08-28 — Raised by the vocabulary audit of stage
  [baseline-capture](transpose-grading-plan.md#baseline-capture)
  ([baseline-vocabulary-audit.md](baseline-vocabulary-audit.md)).
  `beman::transpose::join(MMA&&)` and `Monad::join` are the monadic join,
  `join mma = mma >>= id`; [grade-machinery-home](#grade-machinery-home) gives
  the grade algebra an operation also named `join`, in the same namespace.
  Shallow — a spelling question, not a design one — but cheapest to settle
  before stage [grade-concept](transpose-grading-plan.md#grade-concept) writes
  the name down. Candidates: a nested `grades::` namespace, a `grade_` prefix,
  or members of the `grade_semilattice` model rather than free functions.
  Nothing else collides: `grade`, `semilattice`, `bottom`, `subsume`, and
  `lattice` return zero hits on the public surface.
- 2026-08-28 — Answered: `grade_`-prefixed free verbs, on the
  `monoid_combine` precedent. Divergence closed; work resumed.
- 2026-08-30 — Amended by stage
  [model-dispatched-mixing](transpose-grading-plan.md#model-dispatched-mixing):
  the order question and the value coercion have distinct names.
  `grade_subsumes` is the type-level predicate used in constraints;
  `grade_subsume` is the coercion that re-indexes a carrier at a wider grade.

---

## accumulation-evidence

**Question:** What carries the evidence of *multiple* failures, when the
accumulating applicative object collects every error rather than the first?
**Status:** DECIDED 2026-08-29
**Decision:** The `error_set` value itself, as a **non-empty witnessed subset
of its grade**: for each raised type, one witness value. The grade says "may
raise {A,B}"; the value says "did raise", and did-raise is a subset of
may-raise. Both applicative objects therefore share the carrier exactly as
[applicative-objects](#applicative-objects) states — short-circuit only ever
produces singletons, accumulating combines by witnessed union.
Combining is **left-biased per type**: two A-witnesses keep the first. That is
associative, allocation-free, and deterministic *because*
[applicative-objects](#applicative-objects) already made left-to-right
traversal normative — that decision pays for this one.
Multiplicity loss is real and documented: the second A witness is dropped. The
escape hatch is honest and needs no new machinery — a user who must keep every
witness chooses a collecting error type as their `E`.
**Why:** The alternatives conflated two levels. The grade join is type-level ∪
and is always available, needing no monoid at all; what accumulation needs is
a semigroup on the *evidence*, the value-level record of what did raise.
Requiring `Monoid<E>` on user error types looks for that semigroup in the
wrong place and makes graded accumulation unavailable by construction; its
kernel survives here as "`error_set` supplies the semigroup itself". Making
the accumulating object yield a different carrier was rejected because it
breaks the decided same-carrier premise and makes the result type depend on
the policy, which poisons composition.
The confirming sign that this is the right shape rather than a patch for
accumulation: it makes `recover` compositional. Under one-of semantics,
recovering type A from a value that raised {a,b} has no meaning. Under subset
semantics it is set-difference at both levels — the handler consumes the A
witness, {b} remains an error, empty means success — so the value semantics
and the grade arithmetic become the same operation at two levels.
**Cost:** amends [error-set-identity](#error-set-identity) at the value level:
invariant from "exactly one alternative" to "at least one", storage from a
one-of union to per-type slots (bounded by |grade|, still no allocation, still
constexpr-clean), equality to "same present set, equal witnesses". The
`error_set` shipped by stage
[error-set-type](transpose-grading-plan.md#error-set-type) implements the
one-of form and must be revised before the accumulating object can exist.
**Log:**
- 2026-08-29 — Raised by stage
  [accumulating-object](transpose-grading-plan.md#accumulating-object): the
  plan specified the accumulating object's existence, its grade behaviour, and
  its lawlessness for bind, but never what carries multiple witnesses at the
  value level. The protocol's "question nobody has asked yet" case.
- 2026-08-29 — Answered by Steve.

---

## multi-witness-elimination

**Question:** How is a multi-witness `error_set` value eliminated, now that
`visit` is partial and defined only for the singleton case?
**Status:** DECIDED 2026-08-29
**Decision:** `visit` stays the one-of eliminator — partial, precondition
checked — and is **not** extended to multi-witness. Multi-witness elimination
is a **static per-type fold over the handled set**, implemented as `recover`'s
internal mechanism and **not** shipped as a public verb. The impoverished-API
fence holds until a second client outside `recover` demonstrates the need —
the same YAGNI posture as [datum-entry-point](#datum-entry-point).
**Why:** No runtime visitation verb is required, because the handled set {H}
is a compile-time type-set. Elimination is a static fold over the grade with
runtime presence filtering: for each E in H, if a witness is present, feed it
to the handler and remove it. That is expressible entirely in the API that
already exists — membership plus `witness<E>()` — so a public eliminator would
be machinery with exactly one caller.
Note also that the option one reaches for instinctively — statically excluding
multi-witness visits — does not exist. *Which* witnesses are present is a
runtime property of the value even though the grade is static, so `visit` is
*inherently* partial under the witnessed-subset amendment of
[error-set-identity](#error-set-identity). The only real choice was between a
checked precondition and a silent leftmost pick, and leftmost is a lie: it
reports "the error" of a value holding two.
This retroactively settles the narrowing logged under
[error-set-identity](#error-set-identity). The absent multi-witness visitation
verb is not a gap awaiting a verb; it is the fence line.
**Log:**
- 2026-08-29 — Raised by the `visit` hardening: making the precondition
  checked left the multi-witness case with no visitation verb at all, and it
  was unclear whether that was a hole or a boundary.
- 2026-08-29 — Answered by Steve, deliberately *before*
  [recover-narrowing](transpose-grading-plan.md#recover-narrowing) starts. The
  answer is forced, and under the fresh-agent-per-stage cadence an agent would
  otherwise hit this wall in its first hour and spend a stop-and-report cycle
  on a question that was never open.

---

## golden-vs-scheduled-assertions

**Question:** How does the golden file separate assertions that must never
change from assertions a named stage is *expected* to flip, and what does
[graded-deduction](transpose-grading-plan.md#graded-deduction)'s tripwire say
about the latter?
**Status:** DECIDED 2026-08-29
**Decided by:** Steve Downey.
**Decision:** Separate translation units, and drop the word "golden" for the
scheduled kind. `baseline_deduction.test.cpp` is golden in full: nothing in it
is scheduled to change, and rule 4 applies to all of it.
`current_state.test.cpp` holds assertions that record what the library does
today at a point the plan intends to move; each block names the stage that
will move it. Editing the latter is ordinary work, editing the former is a
stop-and-ask. graded-deduction's tripwire names the distinction rather than
relying on the reader to infer it.
**Why:** A golden is defined by not changing, so an assertion with a scheduled
flip was never one — the fix is the vocabulary, not an exception to the rule.
Separate files make the distinction structural instead of a matter of reading
a comment carefully: "any golden test changes → STOP" stays literally true,
and the scheduled file is visibly droppable. Splitting first also makes the
block available for red/green: flipping the three negatives to their post-
graded-deduction form fails the build today, which is the failure that stage
is defined to fix.
**Log:**
- 2026-08-28 — Raised by stage
  [expected-instance](transpose-grading-plan.md#expected-instance). That
  stage's deliverable asks for "negative tests pinning the mixed case as still
  ill-formed"; [graded-deduction](transpose-grading-plan.md#graded-deduction)'s
  acceptance requires those same mixed cases to become well-formed and deduce
  `expected<T, error_set<E1,E2>>`. Filed as goldens, they make graded-deduction
  trip its own tripwire — "any golden test changes → STOP" — on assertions its
  charter requires it to reverse.
  *Fixed on the test side:* `baseline_deduction.test.cpp` is now split by
  lifetime rather than polarity. Sections 1–8 are goldens; section 9 is
  SCHEDULED, names graded-deduction as its expiry, and carries paired
  permanent controls so the negatives cannot pass vacuously. The split also
  surfaced a misfiling: `!applicative_registered<int>` is permanent and
  load-bearing — under [empty-grade-spelling](#empty-grade-spelling) promotion
  at ∅ must not arrive by registering bare values — yet it sat under a heading
  reading "what is NOT a context today", beside two pins that were about to
  flip.
  *Unresolved, and Steve's call:* graded-deduction's tripwire still says any
  golden change stops the stage, with no mention of a scheduled block.
  Amending a tripwire is what rule 4 forbids and rule 5 reserves, so the plan
  is deliberately left untouched. Options: amend the tripwire to name the
  licensed exception; move the scheduled block to its own file so "golden
  file" stays literally true; or drop the mixed-case negatives from stage 1
  and let graded-deduction assert only the positives.
- 2026-08-29 — Answered: combine the first two — rename away from "golden"
  AND split into `current_state.test.cpp`. Done before graded-deduction
  starts, so the block can be driven red first: the three negatives flipped
  to their post-stage form fail the build at this commit. Divergence closed.
- 2026-08-30 — Narrow ruling by Steve, logged during grading-fidelity
  remediation: after a scheduled block has expired, a stage may append that
  block's positive post-stage form to the golden file only when no existing
  golden assertion is weakened or edited. This retroactively licenses the
  Stage 5 shape; it is not permission to change established golden coverage.

---

## bottom-grade-identity

**Question:** Is the framework's `unit_grade` the same ∅ as a model's
`grade_bottom_t<G>`, or a second bottom sitting below every model's?
**Status:** DECIDED 2026-08-30
**Decided by:** Steve Downey.
**Decision:** The framework ∅ is a pure sentinel, not a grade in any model lattice and not a carrier-bearing bottom.
`grade_of` yields either that ungraded sentinel or a model grade.
Bottoms exist only per model, such as `error_set<>` and `never_fails`.
Promotion is where the sentinel and a model meet: an ungraded operand entering a mixing point lifts to that mixing point's model bottom.
One sentinel, N bottoms, zero duplication.
**Why:** Bare `T` is the unit fiber of every graded family simultaneously, so materializing a framework bottom as if it were a grade with carrier machinery creates a shadow model.
The Boolean model exposed that duplication by forcing the framework bottom and model bottoms to be compared outside the shipped `error_set` vocabulary.
**Log:**
- 2026-08-30 — Raised by stage [law-harness](transpose-grading-plan.md#law-harness).
  Registering the Boolean semilattice as a second model made visible something the shipped model alone hid: the framework and every model each carry their own ∅, and nothing identifies them.
  Each fact below was confirmed by a negative control — invert or delete it, watch the build break, restore.
  * They are DISTINCT TYPES, and STRICTLY ORDERED.
    `unit_grade` and `error_set<>` are not the same type; `grade_subsumes_v<unit_grade, error_set<>>` is true and `grade_subsumes_v<error_set<>, unit_grade>` is false.
    So the framework's ∅ sits strictly BELOW the model's ∅ in the order the framework itself computes.
    A bounded join-semilattice has one bottom; what is registered is the model's lattice with a second bottom glued underneath.
    Everything stays internally consistent — order-from-join is satisfied in both directions — which is why no earlier stage tripped on it.
  * THE ROUND TRIP FAILS AT THE BOTTOM.
    `grade_of_t<rebind_grade_t<T, error_set<>>>` is `unit_grade`, not `error_set<>`, because the ∅ carrier is bare `T` ([empty-grade-spelling](#empty-grade-spelling)) and bare `T` reports the framework's ∅.
    The harness states the round-trip law with that carve-out written into it; removing the carve-out fails the build, so the carve-out is describing reality rather than being defensive.
  * "RE-INDEX AT ∅" IS TWO DIFFERENT FUNCTIONS.
    `rebind_grade_t<expected<int, error_set<A,B>>, unit_grade>` is `expected<int, error_set<A,B>>` — the framework's default leaves a carrier alone.
    `rebind_grade_t<expected<int, error_set<A,B>>, error_set<>>` is `int` — the model's bottom strips the carrier off.
    Under [empty-grade-spelling](#empty-grade-spelling) the second is what ∅ is supposed to mean, so the framework's single carrier-facing default is the one that is wrong for a graded carrier, and a model can only correct it for its own bottom, never for `unit_grade`.
  * THE COST TO A SECOND MODEL, measured.
    The ALGEBRA is ten trivial specializations (four joins, two bottoms, four order facts) and slides in with no friction at all.
    The CARRIER costs four more — `grade_of` on the carrier, promote-bare at ⊤, do-not-nest at ⊤, and strip-to-bare at ⊥ twice, once from the bare value and once from the carrier — and all four are transliterations of `error_set.hpp`'s, with the carrier's name swapped.
    Deleting any one of them breaks the harness.
    The framework supplies exactly one carrier specialization, `rebind_grade<CONTEXT, unit_grade>`, and it is the only one of the five no model needs.
    Two of the model's four exist purely because its ⊥ is not the framework's ∅.
  * THE FAILURE MODE IS BAD.
    Omitting one of those registrations produces `invalid use of incomplete type 'rebind_grade<...>'` pointing inside `grade.hpp`, with nothing naming the registration that is missing.
  * A SENSOR THE HARNESS NOW CARRIES: "one model, one bottom" — every grade in a sample agrees on `grade_bottom_t`.
    `unit_grade` satisfies `grade_semilattice` yet fails this the moment it is admitted to a model's grade sample, which is the cleanest statement of the problem: the framework's ∅ is a grade that belongs to no model's lattice.

  *Not patched, deliberately.*
  Candidate resolutions, none obviously right.
  (a) Identify them: require `grade_bottom_t<G>` to be `unit_grade` for every model, and models stop declaring a bottom type.
  Smallest, and it lets the framework own carrier-stripping once; but it costs `error_set<>` its standing as a grade while keeping it as the explicit uniform spelling, which reaches [empty-grade-spelling](#empty-grade-spelling) and [uniform-form-surface](#uniform-form-surface).
  (b) Keep them distinct but give the framework a constrained `rebind_grade` at any model's bottom, so stripping is written once.
  (c) Accept the duplication and document it as the price of models owning their own lattice.
  Both halves of the disagreement are now pinned by the harness, so whichever is chosen cannot happen silently.
- 2026-08-30 — Ruling by Steve: choose the sentinel interpretation, not identification and not documented duplication.
  Framework-∅ is the model-less state "not yet in a family"; model bottoms remain model-owned.
  The repair belongs in stage [model-dispatched-mixing](transpose-grading-plan.md#model-dispatched-mixing), where promotion at a mixing point lifts ungraded operands to that point's model bottom.
- 2026-08-30 — Implemented by stage [model-dispatched-mixing](transpose-grading-plan.md#model-dispatched-mixing).
  `unit_grade` no longer models `grade_semilattice`, `rebind_grade<CONTEXT, unit_grade>` no longer exists, and implementation helpers lift the sentinel to the current model's bottom only inside model-dispatched joins.

---

## mixing-point-vocabulary

**Question:** In whose vocabulary is the join at a mixing point computed —
the framework's `grade_join`, or the model's own?
**Status:** DECIDED 2026-08-30
**Decided by:** Steve Downey.
**Decision:** Fix the mixing point rather than documenting around it.
Mixing-point deduction is `rebind_grade<Carrier, grade_join<g1, g2>>`, dispatched through the operands' grade model.
No shipped mixing-point code utters `error_set` outside the model layer.
If an ungraded operand participates in a typed mixing point, it is first lifted to that point's model bottom as decided by [bottom-grade-identity](#bottom-grade-identity).
**Why:** [grade-generality](#grade-generality) says `error_set` is one model of a grade concept, and the Boolean model proved that the current deduction path registers a second algebra without letting it drive the machinery.
The repair must happen while Steve is still the sole client, because after a second client this change would alter meanings rather than only repair an abstraction boundary.
**Log:**
- 2026-08-30 — Raised by stage [law-harness](transpose-grading-plan.md#law-harness), and it is the sharp half of what the second model was put there to detect.
  [grade-generality](#grade-generality) decides that the framework layer speaks only grade vocabulary.
  That holds for the algebra and the carrier traits — see the leak-detector entry logged there.
  It does not hold at the mixing point.
  * `grade_join_t` HAS NO CALLERS.
    Not one, anywhere in `include/`.
    The only framework verb any shipped header consumes is `grade_subsume`, in the defaulted `subsume` member of the two CRTP bases.
    Every join a graded deduction actually performs runs through `detail::joined_error_t` in `expected.hpp`, written end to end in error vocabulary (`error_elements`, `error_set_of_elements`, `error_set<...>`).
    The framework's join verb is registered by the model, asserted by tests, and used by nothing.
  * WHERE THEY AGREE, THEY AGREE BY CONSTRUCTION.
    For two operands that are already graded, the deduced result's grade equals `grade_join_t` of the operand grades.
    That is now pinned as a sensor — but it is agreement, not dispatch, and a second algebra gets no benefit from it.
  * WHERE THEY CANNOT AGREE.
    Lazy join ([grading-footprint](#grading-footprint), no spontaneous singletons) makes `grade_of_t<expected<int, errc>>` equal `unit_grade`.
    So for the bare mixing point the framework's verbs compute ∅ ∨ ∅ = ∅ and predict a bare `int`, while the instance deduces `expected<int, error_set<errc, io_errc>>`.
    The step the instance takes and the grade layer cannot express is LIFTING A BARE ERROR TYPE INTO A SINGLETON SET — which is error vocabulary by definition.
    This is not a bug in either layer; it is the observation that the newly-claimed territory of [grading-footprint](#grading-footprint) is reachable only in the model's language.
  * THE PRACTICAL CONSEQUENCE.
    A second algebra can be REGISTERED but not USED.
    The Boolean model passes every law in the harness and still cannot participate in a graded deduction, because the graded core of `ExpectedApplicativeImpl` produces an `error_set` regardless of which algebra the operands' grades belong to.
    "An abstraction with one model is renamed, not generic" is the test [grade-generality](#grade-generality) set for itself; on this reading the abstraction currently has one model at the layer that matters.

  *Steve's call, and it may re-open a DECIDED entry.*
  Logging rather than stopping is what stage [law-harness](transpose-grading-plan.md#law-harness) instructs for exactly this finding, so the stage completed; but this contradicts the letter of [grade-generality](#grade-generality), which is more than a stage-local divergence.
  *Not patched:* routing the mixing point through `grade_join` needs the grade layer to gain something the ∅ grade currently forbids — either a singleton-lifting operation, or a `grade_of` that reports a singleton for `expected<T,E>`, which [grading-footprint](#grading-footprint) rules out at the deduction level even if not necessarily at the trait level.
  Either is a design decision, not a stage deliverable.
- 2026-08-30 — Ruling by Steve: this is a design bug with the same root cause as [bottom-grade-identity](#bottom-grade-identity), not an acceptable documented limitation.
  The next stage must make the Boolean model drive an actual mixed deduction before [paper-revision](transpose-grading-plan.md#paper-revision) starts.
- 2026-08-30 — Implemented by stage [model-dispatched-mixing](transpose-grading-plan.md#model-dispatched-mixing).
  The aborted `mixing_grade` direction was removed; mixing deductions use `grade_of`, same-model checks via `grade_model`, and `grade_join_t` folded over operands after lifting only ungraded operands to the current model bottom.

---

## cross-model-mixing

**Question:** May a mixing point combine graded operands from different grade models?
**Status:** DECIDED 2026-08-30
**Decided by:** Steve Downey.
**Decision:** No.
Both graded operands at a mixing point must belong to the same grade model; cross-model mixing is ill-formed by constraint.
Do not build product-of-models machinery.
**Why:** Model-dispatched mixing needs one model to supply the join and bottom-lift vocabulary for the deduction.
A product of grade models is a new semantic feature with no current client, the same YAGNI boundary recorded for fuel and other perpendicular axes in [grade-generality](#grade-generality).
**Log:**
- 2026-08-30 — Raised and answered by Steve's ruling on the Stage 8 leak-detector findings.
  The absence of cross-model products is intentional and belongs in the log so the next stage treats it as a constraint, not an oversight.
- 2026-08-30 — Grading-fidelity review found a constraint divergence in
  expected's same-error-plus-bare cores: "bare" meant "not `std::expected`,"
  so a foreign graded carrier could enter the lazy expected path and bypass
  the same-model check. Fixed by making "bare" mean semantic ungraded
  (`grade_of_t<T> == unit_grade`, spelled through `graded_context`) while
  preserving declared-error matching for the unmixed expected spelling.

---

## evidence-combine-surface

**Question:** What public surface combines value-level failure evidence for
the accumulating expected applicative object?
**Status:** DECIDED 2026-08-30
**Decided by:** Steve Downey.
**Decision:** There is no generic public `combine_errors`.
The shipped error-set model exposes its native `error_set_combine` operation.
Framework-facing evidence dispatch stays private as
`detail::combine_grade_evidence`, with a left-biased same-type default and
model-specific overloads where needed.
**Why:** Evidence combination is value-level model vocabulary, not a generic
grade-algebra operation. A public generic name would either encode the
shipped model's assumptions as framework API or promise a cross-model
semigroup the grade concept does not require.
**Log:**
- 2026-08-30 — Raised by the grading-fidelity review.
  Stage accumulating-object introduced public `combine_errors`, but the later
  model-dispatched repair moved the only framework fold to
  `detail::combine_grade_evidence`, leaving `combine_errors` and its support
  trait `is_error_set_of_v` as caller-less residue. They were removed; the
  intentional public model-native operation remains `error_set_combine`.

---

## graded-context-role

**Question:** Is `graded_context` the public spelling of
[grading-footprint](#grading-footprint)'s graded/ungraded exclusivity
constraint?
**Status:** DECIDED 2026-08-30
**Decided by:** Steve Downey.
**Decision:** Yes.
`graded_context<C>` means `grade_of_t<C>` is a model grade rather than the
framework's ungraded sentinel. It is public semantic vocabulary, and shipped
mixing-boundary constraints use it to distinguish true ungraded operands from
foreign-model carriers.
**Why:** Structural checks such as "not `std::expected`" or "contains
`error_set`" do not survive multiple grade models. `graded_context` is the
single framework question that matches the sentinel/model split decided by
[bottom-grade-identity](#bottom-grade-identity).
**Log:**
- 2026-08-30 — Raised by the grading-fidelity review after `graded_context`
  was public and tested but unused in shipped headers. The expected
  same-error-plus-bare constraints now make it load-bearing: plain `int`
  remains bare, `expected<T, E>` keeps the declared-error lazy spelling path,
  and `Fallible<T, may_fail>` is rejected at the expected cross-model
  boundary.

---

## wording-generation

**Question:** Where does P3200's normative wording come from, and how does it
reach the paper?
**Status:** DECIDED 2026-09-03
**Decision:** The shipping headers are the wording source.
`beman.specgen` reads each in-scope header on its own and renders mpark/wg21
markdown fragments into `papers/wording/`; `D3200R0.md` splices them with a
per-paper pandoc filter, `papers/filters/transclude.py`, selected by
`papers/defaults.yaml`.
`make wording` regenerates, `make wording-check` is the drift gate, and the
fragments are checked in so the paper builds without specgen installed.
**Why:** Hand-written wording drifts from the reference implementation it
claims to specify, and the drift is invisible until review. Generating it
means the paper cannot describe an operation the code does not have.
Splicing through a per-paper filter keeps the MPark.WG21 subtree unpatched, so
`git subtree pull` costs nothing.
**Consequences:** specgen reads only the main file's declaration/comment
interleave, so each header contributes its own synopsis subclause rather than
there being one `[transpose.syn]`. Marked-up headers declare members in-class
and define them out of line, so that a member's wording is placed by the
definition's lexical position.
**Log:**
- 2026-09-03 — Decided, and the pipeline built for the eight in-scope headers.
- 2026-09-04 — Regenerated against a specgen carrying eight fixes
  (steve-downey/specgen#1 and #3--#8). The generated wording had been wrong in
  ways the old tool could not see, and the checked-in fragments carried every
  one of them: a dozen documented namespace-scope aliases, variable templates
  and concepts rendered as *empty* code blocks with their descriptions
  discarded (#1); `\expos` on a namespace-scope alias was inert, so
  `traverse_context_t` published its underscore spelling rather than
  `traverse-context-t` (#1 follow-up); `\seebelow` on `recover` was inert
  against an explicit trailing return type (#6); and `grade_lifted_into_model`
  published a stray `public:` above a `type` naming an elided private alias,
  which would not compile if copied (#7). Four error-severity findings and
  four synopsis defects were fixed in the markup: the `detail` machinery each
  header declares is now `\omit`ted rather than published as specification
  (#3 made the leak visible by reporting a qualifier wherever its namespace is
  declared, not only in the main file), `error_set`'s canonicalizing
  right-hand side is masked with `\seebelow`, `applicative_eval` gained a
  namespace-scope spelling under
  [wording-visible-internals](#wording-visible-internals), and two
  `// NOLINT` comments stopped rendering into the published `error_set_of`
  synopsis. Two rules this decision imposed are relaxed: an in-class body is
  now spliced out of the synopsis whichever entities it names (#5), and a
  `\rSec` title may wrap across `//` continuation lines (#8).
- 2026-09-04 — Raised while regenerating and filed as
  steve-downey/specgen#18: a documented class or class-template *definition*'s
  own description elements were silently discarded. The `\remarks` on
  `unit_grade` and on `grade_of`, and the `\mandates` and `\remarks` on
  `error_set_of`, appeared in no generated fragment, and the authored
  `\mandates` did not replace the derived one. The silent-drop family #1
  closed for namespace-scope entities, which the #1 backstop missed because a
  definition does produce a synopsis.
- 2026-09-05 — Regenerated against a specgen carrying seven further fixes
  (steve-downey/specgen#18, #20--#24 and #31). #18 is the one that moved this
  paper: all four dropped descriptions now render, and `error_set_of`'s
  authored *Mandates* replaces the derived paragraph, so the canonical-pack
  requirement the class exists to enforce is finally stated in the terms it was
  written in. Nothing else in the wording moved, and no new finding appeared.
  Four of the remaining six fixes address shapes this markup does not have --
  transpose spells every constraint as a trailing requires-clause rather than
  in the template head (#20), defines no member in class (#21), declares no
  deduction guide (#22), and marks no class template `\expos` (#23) -- and #31
  concerns gathered regions. #24 is the one with leverage: bare `\seebelow`
  now masks a namespace-scope variable's type, so `applicative_eval` is
  described as `inline constexpr unspecified applicative_eval;` rather than
  `\omit`ted, and a name the synopsis puts in front of a reader is one the
  reader can now look up. Masking a *reference*-typed variable renders a stray
  `const` and loses a space (steve-downey/specgen#33), so it is declared as a
  forwarding object rather than a forwarding reference.
- 2026-09-06 — Regenerated against a specgen carrying seven more fixes
  (steve-downey/specgen#33--#41 and #47's qualifier normalization). The one
  that matters is #36: `\expos` now reaches a declaration in an included
  header, which reverses
  [wording-visible-internals](#wording-visible-internals) and removes ten
  namespace-scope spellings the pipeline had added to the library. #33 fixed
  the reference mask filed from here, though `applicative_eval` stays a
  forwarding object: it reads as the same thing and there is no reason to churn
  it back. #47 moved nothing, these headers being west-const throughout. Two
  new gaps went the other way and are filed rather than worked around:
  steve-downey/specgen#49, a partial specialization of an `\expos` primary
  rendering its raw name -- visible in `transpose.errset.recover.md`, where
  `is_expected_v`'s specialization sits unrenamed under its own
  `$is-expected-v$` primary -- and steve-downey/specgen#50, `\expos` and
  `\seebelow` not composing on an alias or a concept, which is what would end
  the three exposition-only chains that still name an undeclared helper.
- 2026-09-06 — Rechecked against the next beta (fba1271). Its one functional
  change is steve-downey/specgen#45, which concerns gathered regions this
  pipeline does not use, and the generated wording is byte-identical. Two
  defects found by reading the output rather than by the validator, both filed
  and neither worked around: steve-downey/specgen#56, a class template's
  parameter list keeping `std::` in the synopsis while the next line of the
  same code block drops it -- visible in `transpose.array.syn.md` against
  `transpose.array.tuple.md` -- and steve-downey/specgen#57, the `--paper`
  paragraph-number placeholders restarting at `x` in every wording block, which
  gives `[transpose.grade.syn]` nine paragraphs all numbered `x`. Spelling
  `size_t` unqualified in `array.hpp` would silence the first, and that is the
  edit [wording-visible-internals](#wording-visible-internals) now refuses to
  make: the specification does not get to change the library to suit itself.

- 2026-09-06 — Regenerated against the beta that closes every issue filed from
  here (steve-downey/specgen#48--#50, #56, #57). All four defects this paper
  carried are gone: the `[x]` placeholders now run ascending across a whole
  subclause, so `[transpose.grade.syn]`'s nine paragraphs are `x` through
  `x+8` rather than nine `x`s; `ArrayApplicativeImpl`'s head reads
  `template<class T, size_t N>`; and `is_expected_v`'s specialization renders
  under its primary's exposition name.
  The markup adapts to two of them rather than only benefiting. #49 lets a
  specialization follow its `\expos` primary, so the two-case helpers
  `carrier_value` and `mixes_with_model_impl` are exposed whole instead of
  `\omit`ted whole -- an exposition-only primary and the specialization
  carrying the real case, which is what such a helper looks like in the draft.
  #50 lets `\seebelow` mask an alias's definition under `\expos`, which ends
  the one chain that does not terminate usefully: `mixed_result_t` now renders
  `= see below` rather than opening four levels of grade-algebra plumbing to
  say one thing about a return type. **No raw implementation name reaches the
  wording any more**, and every exposition-only name in the document is
  declared in it -- the residue this log recorded on 2026-09-05 is closed.
  One cosmetic defect remains, filed as steve-downey/specgen#67: an
  exposition-only rename does not re-flow a continuation line, so the second
  line of `mixes-with-model`'s definition sits nine columns short of its
  arguments.

---

## wording-visible-internals

**Question:** specgen refuses to render a declaration that carries a
`beman::transpose::detail` qualifier. What gives way -- the header layout, or
the wording?
**Status:** DECIDED 2026-09-03; reversed 2026-09-05
**Decision:** The wording. A `detail` entity that appears in a *declaration*
the specification shows -- a constraint, a template-parameter default, or a
trailing return type -- is marked `\expos` where it is defined, and its uses
render as the exposition-only spelling. The header layout is unchanged and the
namespace is not widened. Machinery below an exposition-only entity is
`\omit`ted. Bodies keep their `detail` spellings, because a body specgen does
not render cannot leak.
The original answer was the header layout, and stood while specgen could not
read a marker on an entity it was not specifying; the log records the reversal.
**Why:** A generated specification should not be able to require an edit to
the thing it specifies. Every forwarding spelling was a public name the library
did not want, added to satisfy a tool, and the names were real: they changed
lookup and ADL, and nothing outside the headers ever used them. Marking the
entity where it lives says the same thing to the reader -- the standard has no
`detail` namespace, so a declaration that names one is not specification text
-- and says it without moving anything.
**Consequences:** the following are `\expos` where they are defined, in
`beman::transpose::detail` unless noted. Their uses render as the
exposition-only spelling and no public name is added:
`is_expected_with_error_v`, `bind_result_t`, `all_declare_v`,
`declares_or_bare_v`, `all_declare_or_bare_v`, `carrier_value_t`
(`expected.hpp`); `mixes_with_model`, `mixed_result_t` (`grade.hpp`);
`error_set_is_canonical_v`, `error_set_names_distinct_v`, `recover_return_t`
(`error_set.hpp`); and `applicative_eval`, which stays in `beman::transpose`
under `\seebelow` because the wording describes it rather than only naming it
(`apply.hpp`). `traverse_context_t`, `is_expected_v` and `error_set_has_v` stay
where they are: the first two because the wording shows their declarations, and
`error_set_has_v` because it also answers a language problem -- one spelling of
the membership constraint usable both in class and on an out-of-line
definition, where class scope is not in effect.
Three exposition-only definitions name an entity the document does not declare:
`carrier_value_t` names `carrier_value`, `mixes_with_model` names
`mixes_with_model_impl`, and `mixed_result_t` names `mixed_grade_t`. Each is a
helper whose own definition would drag in more machinery than it settles, and
the marker that would end the chain -- `\seebelow` on an exposition-only alias
-- does not compose yet (steve-downey/specgen#50).
**Log:**
- 2026-09-03 — Raised while marking up `traverse.hpp`. `\verbatim-itemdecl`
  was tried first and emits *both* the authored declaration and the parsed
  one, which is a specgen defect (steve-downey/specgen#4, reproducible in ~15
  lines). `\verbatim-synopsis` has the same defect, and that is the one that
  would have mattered: most of the leakage errors here were on the class
  synopsis, which `\verbatim-itemdecl` does not reach. `\expos` does not
  remove a `detail` qualifier, since the entity is still in `detail`, and
  `\seebelow` masks a return type rather than a constraint, so the entity
  itself has to move or be forwarded. A working `\verbatim-synopsis` plus an
  authored `\constraints` would have avoided every promotion listed above.
- 2026-09-04 — The premise has been superseded and the decision is retained
  anyway. Both verbatim markers now replace the extracted declaration instead
  of duplicating it (steve-downey/specgen#4), and bare `\seebelow` now reaches
  an explicit trailing return type (#6), which alone would cover
  `recover_return_t`, `carrier_value_t`, `bind_result_t` and `mixed_result_t`.
  So the trigger this entry names has fired: masking a constraint in a
  synopsis is now possible. It is not being taken, because the way to take it
  is `\verbatim-synopsis`, and an authored synopsis is a hand-maintained one —
  reintroducing, for exactly the classes most worth generating, the drift
  [wording-generation](#wording-generation) exists to prevent. `\seebelow` is
  being taken where it masks rather than replaces: `error_set`'s
  canonicalizing right-hand side, and `recover`'s trailing return type, whose
  marker had been inert since it was written. Unwinding the remaining
  promotions is a live option and a separate change; the count grew by one
  first, because `applicative_eval` was leaking through a hole in the leakage
  checker (#3) rather than being caught and forwarded like its siblings.
- 2026-09-05 — REVERSED. steve-downey/specgen#36 makes `\expos` reach a
  declaration in an included header, so the marker can be written on the
  `detail` entity itself and its uses render as the exposition-only spelling
  with no qualifier and no finding. That removes the whole reason the header
  had to give way. Ten forwarding spellings are gone -- six deleted from
  `expected.hpp`, three moved back into `detail` in `error_set.hpp`, and
  `carrier_value_t` -- with the uses re-qualified to `detail::`, which is where
  they were before the pipeline existed. Nothing outside the headers referenced
  any of them: the one test that touches this machinery
  (`laws.test.cpp:274-286`) already spelled it `detail::mixes_with_model` and
  `detail::mixed_result_t`. The wording is better for it, not merely no worse:
  a constraint that used to name a bare `all_declare_v` now names
  `$all-declare-v$`, which the same document declares as exposition-only. The
  issue's own commit message names this project's #3 workaround as the thing
  that put the entities out of reach, so the reversal is the report closing its
  own loop.
- 2026-09-05 — One promotion stops being a bare `\omit`. Bare `\seebelow` now
  masks a namespace-scope variable's declared type (steve-downey/specgen#24),
  so `applicative_eval` is described as `inline constexpr unspecified
  applicative_eval;` instead of being omitted. That is a better answer than
  either horn of this question: the synopsis shows the name in `ap`'s
  constraint, and the reader can now find out what it is without the wording
  claiming a type for it. The rest of the list is unchanged -- masking a
  variable does not help a trait whose *value* is the point, and
  `error_set_is_canonical_v` rendered as `unspecified` would be worse than
  omitted.

---

## wording-spec-names

**Question:** Are the reference implementation's spellings the ones the
wording should use?
**Status:** OPEN
**Decision:** Deferred for R0.
`Applicative`, `Traversable`, `applicative_typeclass`,
`OptionalApplicativeMap` and their siblings are implementation names; WG21
wording is lowercase and would not name a CRTP base this way. The explicit
object parameter (`this auto&& self`) likewise appears in every generated item
declaration and would not appear in a specification.
**Why:** The naming discussion is a paper-level argument, not a markup
question, and settling it before the mechanism has been reviewed would spend
the discussion twice. D3200R0 says so in the wording preamble rather than
shipping the spellings as if they were settled.
**Log:**
- 2026-09-03 — Recorded when the wording pipeline landed.

---

## monoid-carrier-canonicity

**Question:** Which carriers get a default `Monoid<T>` registration, and
which are named instead?
**Status:** DECIDED 2026-09-07
**Decided by:** Steve Downey, in the typeclass-relationships design
discussion of 2026-09-07, recorded in
`docs/coordination-worklist-2026-09-07.md`.
**Decision:** A raw carrier gets a default `Monoid<T>` registration only where
one instance is canonical: string and vector concatenation, and `Count`.
Where no instance is so right that any one of them can be the default —
numbers, booleans — the choice is spelled by a named carrier type instead of
a registration on the bare type.
**Why:** Addition and multiplication are both monoids on a number; maximum
and minimum are both monoids on any ordered type; a `bool` carries both
conjunction and disjunction. Registering one of these as `Monoid<int>` or
`Monoid<bool>` makes the library pick for the caller, silently, at every
`fold_map` whose function happens to return that type. Naming the carrier —
`Sum<int>`, `Max<int>`, `Any` — makes the choice something the caller writes
down instead.
**Log:**
- 2026-09-07 — [named-monoid-carriers](../tmp/plan/step-named-monoid-carriers.md)
  added the six named carriers (`Sum`, `Product`, `Max`, `Min`, `Any`, `All`)
  to `monoid.hpp`, and moved `fold.hpp`'s `detail::Any`/`detail::All` onto the
  new public `Any`/`All` so `any_of`/`all_of` exercise them. The carrier set
  is provisional: six because these are what the fold family and the
  worklist named; a consumer needing a seventh (`First`, `Last`, `Endo`)
  extends the set rather than working around it. The bare-numeric
  `Monoid<int|long|size_t>` registrations are still present; removing them is
  the following step,
  [numeric-monoid-defaults](../tmp/plan/step-numeric-monoid-defaults.md).
- 2026-09-07 — [numeric-monoid-defaults](../tmp/plan/step-numeric-monoid-defaults.md)
  removed the three bare-numeric `Monoid<int>`, `Monoid<long>`, and
  `Monoid<std::size_t>` registrations from `monoid.hpp`. The only in-tree
  consumer was `monoid.test.cpp`'s additive-int `TEST_CASE`, migrated to
  `Sum<int>`. The sentinel is a `has_monoid` concept with
  `static_assert(!has_monoid<int>)` (and `long`, `std::size_t`), so a future
  re-registration fails a test instead of silently restoring the old default.

## impl-access-through-bases

**Question:** How does a derived member of a typeclass base (`Functor`,
`Applicative`, `Monad`, `Foldable`, `Traversable`) address its `Impl`, given
that `self` is a deducing-this parameter typed as the most-derived class —
which may be a `Map`, a user class, or another typeclass object wrapping this
one?
**Status:** DECIDED 2026-09-07
**Decided by:** Steve, for the half that keeps `protected`: the published
wording is not changed as a side effect of an implementation convenience.
`struct Applicative : protected Impl` and `struct Traversable : protected
Impl` are published wording, appearing verbatim in
`papers/wording/transpose.applicative.syn.md` and
`transpose.traversable.syn.md`, generated from these headers, so the
inheritance keyword itself is out of scope for any refactor. The mechanism
that reaches `Impl` under that constraint is decided by this step, from
compile evidence gathered in the amendment consult's throwaway worktree.
**Decision:** Three parts, all needed by later steps:
- The five bases keep `protected Impl`. Not renegotiable by a later step:
  `Applicative` and `Traversable`'s class heads are published, and changing
  the inheritance changes what D3200R0 proposes.
- Addressing goes through **`impl_of(self)`, a private member of each
  base**, with the const rule shared as `impl_ref_t` in
  `include/beman/transpose/detail/typeclass_base.hpp`. A namespace-scope
  helper cannot perform the conversion, because it is a member or friend of
  nothing, and under protected inheritance only a member of the base that
  owns the `Impl` sub-object may cast to it.
- **A base exposes an operation as its own member, never as a `using
  Impl::op;` re-export, wherever that base may itself be wrapped.** This is
  the half that keeps a two-deep composition (`Functor<SomeMonadMap>`, where
  `SomeMonadMap` is itself built from `Monad<Impl>`) reachable: an external
  call enters the outer base's own member, which hands the inner base's
  member a `self` typed as the `Map` — one level deep, where addressing
  already works. If a later step turns a probing member back into a
  re-export, the deep chain re-forms and the inner base's `impl_of` sees a
  `self` typed as the *outer* wrapper instead of the `Map`, and the cast
  fails: `'X' is an inaccessible base of 'Functor<SomeMap>'`, raised from
  inside the inner base's member.
**Why:** Measured, with the inheritance untouched:
- A namespace-scope helper performing `static_cast<Impl &>(self)` fails
  access control even one level deep — it is a member or friend of nothing,
  and protected base-class accessibility has no clause that walks upward
  into it.
- A member of an *inner* base cannot touch an *outer* object's inherited
  surface at all: `Monad<Impl>` is a base of `Functor<Map>`, not a friend or
  member of it, and base-class accessibility does not walk upward.
- A `using Impl::op;` re-export at the wrapping base fails the two-deep case
  specifically, with `'Probe' is an inaccessible base of 'Outer<InnerMap>'`
  (reproduced directly in
  `tests/beman/transpose/detail/typeclass_base.test.cpp`'s two-deep
  `TEST_CASE`s, which use the own-member shape and pass; the re-export
  failure itself is documented here rather than compiled, since it is a hard
  error rather than a SFINAE-friendly one).
- The full suite is green and unchanged after converting
  `Applicative<Impl>::invoke`, `Applicative<Impl>::ap`, and
  `Monad<Impl>::invoke` from the open-coded `SELF`/`IMPL_BASE` cast to
  `impl_of(self)` — same probes, same derivations, same passing count
  (119, then 124 with this step's five added `TEST_CASE`s exercising the
  mechanism directly).
- The generated wording is byte-identical: `scripts/gen-wording.sh` produced
  a diff against only the four fragments already known to drift for
  unrelated reasons (`transpose.errset.recover.md`,
  `transpose.errset.syn.md`, `transpose.expected.syn.md`,
  `transpose.grade.syn.md`); neither `transpose.applicative.syn.md` nor
  `transpose.traversable.syn.md` appears. `impl_of` is `//! \omit`-marked and
  in a trailing private section in `apply.hpp` and `traverse.hpp`, which
  renders as nothing.

A trailing *requires-clause* is not a complete-class context, so `impl_of`
cannot be named there: `Applicative<Impl>::ap`'s declaration-level
disjunctive `requires`-clause keeps its existing `requires(const Impl &impl)
{ impl.op(...); }` form rather than being rewritten to name `impl_of`.
Member *bodies* are complete-class contexts and use `impl_of(self)` freely;
this split — declaration clauses one way, bodies another — is the shape
every later probing member copies.

**Provisional:** the cast is repeated in five classes rather than shared.
What would justify sharing it is a language change that lets a non-member
perform the conversion, or a base gaining genuinely private state, which no
typeclass object has today — every one of them is stateless and empty. What
is not repeated is the const propagation, which lives once in `impl_ref_t`.
**Log:**
- 2026-09-07 — [impl-probe-helper](../tmp/plan/step-impl-probe-helper.md)
  added `impl_ref_t` to `detail/typeclass_base.hpp` and a private `impl_of`
  to each of `Functor`, `Applicative`, `Monad`, `Foldable`, `Traversable`,
  then converted the three existing native-`Impl` probes
  (`Applicative<Impl>::invoke`, `Applicative<Impl>::ap`,
  `Monad<Impl>::invoke`) to call through it. Pure refactor: no other member
  gained a probe, no `: protected Impl` changed, no `using Impl::op;`
  re-export changed. The own-member rule (this decision's third part) is
  applied to a real member for the first time by
  [monad-fmap-basis](../tmp/plan/step-monad-fmap-basis.md), the next step.

## functor-monad-grounding

**Question:** How does a type with a `Monad` instance and no separate
`Functor` registration obtain its `fmap`, given that `fmap f x == bind(x,
pure . f)` is a theorem rather than a coincidence?
**Status:** DECIDED 2026-09-07
**Decided by:** the design, applied by
[monad-fmap-basis](../tmp/plan/step-monad-fmap-basis.md).
**Decision:** Structurally, not by a superclass constraint. `Monad<Impl>`
provides the Functor **basis** operation, `fmap`, derived as `bind(ma, pure .
f)` with native preference for an `Impl::fmap` when the instance supplies
one. The full Functor instance is then spelled at the registration or call
site as `Functor<SomeMonadMap>{}` — no adapter type, no nominal wrapper
requirement. The CRTP base is the adapter.

**Monad grows only the basis operations of the classes it can ground, never
their derived operations.** `replace` stays on `Functor<>` and is reached
through the layered instance, not duplicated onto `Monad`. This is what
keeps a monad-grounded instance tracking Functor's derived surface instead
of forking from it as that surface gains operations.

**Why:** Conformance in this library is structural throughout — provide the
operations, claim the laws at the registration site — so a superclass
constraint would be foreign to the rest of the design where a theorem
suffices. Growing only the basis, and never the derived surface, is the rule
that keeps the two typeclasses from drifting: if `Monad` also grew `replace`
directly, a change to `Functor::replace`'s derivation would have to be
mirrored onto `Monad` by hand, and nothing would catch a missed mirror. The
agreement test in `laws.test.cpp` is the sentinel: where a hand-written
`Functor` and a `Monad` coexist on the same carrier (`std::optional`), the
hand-written `fmap` and the Monad-derived one are checked equal, so the
redundancy cannot drift silently.

`fmap`'s `requires`-clause is a disjunction — native `Impl::fmap`, or
`Impl::bind` — spelled in the `Applicative<Impl>::ap` shape from
`apply.hpp`, for the same reason: an unconstrained probing member is
satisfied by substitution alone, so a later deep object concept checking for
`fmap` would find it vacuously present even when neither `Impl` operation
exists. Both branches address `Impl` directly, never `self` — `fmap` and
`bind` are one of the mutually-derivable pairs (`bind` is recoverable from
`join` + `fmap`) that `apply.hpp`'s cycle discipline exists to keep from
recursing into each other, and generalizing Impl-direction to other members
is out of scope for this decision.
**Log:**
- 2026-09-07 — [monad-fmap-basis](../tmp/plan/step-monad-fmap-basis.md) added
  `fmap` to `Monad<Impl>` and converted `Functor<Impl>::fmap` from a `using
  Impl::fmap;` re-export to its own forwarding member — the own-member rule
  from [impl-access-through-bases](#impl-access-through-bases), applied to a
  real member for the first time. That conversion is what makes
  `Functor<OptionalMonadMap<int>>` compile at all: with the re-export, an
  external call landed directly in `Monad<Impl>::fmap` with `self` typed as
  the outer `Functor<...>`, where the protected-inherited `Impl` is
  unreachable (`'OptionalMonadImpl<int>' is an inaccessible base of
  'Functor<OptionalMonadMap<int>>'`); with `Functor` owning the member, the
  call enters `Functor::fmap` first, where the conversion is accessible, and
  hands `Monad<Impl>::fmap` a `self` typed as the `Map` — one level deep,
  where addressing already works. Surfaced along the way: `OptionalMonadImpl
  ::bind` computed its result type only in the body (bare `auto`, `using
  Result = ...std::invoke_result_t<F, const A &>...`), which is exactly the
  non-SFINAE-friendly shape `apply.hpp`'s basis invariant warns against —
  probing it from `fmap`'s disjunctive `requires`-clause with an
  incompatible `F` produced a hard error rather than a clean constraint
  failure. Given a trailing return type (`-> remove_cvref_t<
  std::invoke_result_t<F, const A &>>`), the probe fails cleanly, matching
  the invariant `apply.hpp` already states for `Applicative` impls. Suite
  went from 124 to 131.

## derived-op-native-preference

**Question:** How does a derived operation on a typeclass base find a
better native implementation, and what may it address?
**Status:** DECIDED 2026-09-07
**Decided by:** the design, applied by
[functor-monad-derived-probing](../tmp/plan/step-functor-monad-derived-probing.md).
**Decision:** Two parts.
1. Every derived member probes `Impl` for a native version and forwards to
   it when present, deriving otherwise, and carries a disjunctive
   `requires`-clause: native present, or the derivation's own requirement on
   the basis holds.
2. **A derived member's second alternative must name the same expression
   its body's derivation branch evaluates — same receiver, same spelling.**
   An alternative may address `Impl` only if the operation it names is one
   `Impl` is required to supply directly: a hard requirement, or the other
   half of a mutually-derivable pair — `invoke`/`ap`, `fold_map`/
   `fold_right`, `bind`/`join`+`fmap`. Anything the base can *synthesize* is
   addressed through `self`.

`Functor::replace`, `Monad::join`, `Monad::kleisli` and `Monad::ap` all
adopted the shape. `join`/`bind` is one of the mutually-derivable pairs, so
its derivation addresses `impl_of(self).bind(...)` directly, matching
`fmap`'s bind-basis branch; `replace`, `kleisli` and `ap`'s bind + pure
derivation are one-way and keep routing through `self`. `subsume` and
`bind_with` were deliberately left unprobed: `subsume` is grade machinery
defaulted from the algebra, not a derivation over `Impl`, and `bind_with` is
explicit delegation to an object the caller passed — neither has an `Impl`
operation to prefer.

**Not every member has an expressible second alternative.** `kleisli`
returns a closure whose body calls `bind` on an argument type ("a") that is
not known until the closure is invoked, so there is no concrete expression
to probe at `kleisli`'s own instantiation. `bind`'s existence is already
guaranteed unconditionally by `Monad<Impl>`'s class invariant (the
`static_assert` plus `using Impl::bind;` at the top of the class fail the
whole class before `kleisli`'s clause is ever reached if `Impl` lacks
`bind`), so `kleisli`'s second alternative is spelled `true` rather than a
tautological re-check. `invoke`'s second alternative could not name
`FUNCTION` directly either — its arity does not match `bind`'s
single-argument callback shape, since the derivation applies it only after
unwinding nested `bind` calls — so it probes `impl.bind(first, <a
single-argument passthrough lambda>)` instead, checking that `FIRST` is
bind-compatible without asserting anything about `FUNCTION`.

**Why:** The constraint keeps the deep object concept a later step
introduces from being satisfied vacuously by substitution alone, and
restores "missing basis" as a clean constraint failure. The pairs-only rule
keeps `Map`-level shadows at exactly their current reach — broad
Impl-direction would let external calls hit a shadow while internal
derivations skipped it. Hand-rolled objects never touch the bases and are
unaffected.

**Record as provisional:** which pairs are mutually derivable is a fact
about the current basis sets, and admitting an alternate Monad basis would
add one.
**Log:**
- 2026-09-07 —
  [functor-monad-derived-probing](../tmp/plan/step-functor-monad-derived-probing.md)
  converted `Functor::replace` and `Monad::join`/`kleisli`/`ap`/`invoke` to
  the probe-then-derive shape and added preference tests, including one
  per-instantiation test (`Monad::join` native for
  `std::optional<std::optional<int>>` only, falling back for
  `std::optional<std::optional<std::string>>` on the same Map) exercising
  the property a Map-level `using`-declaration could never express. No
  `Map`'s `using`-declarations were removed. Suite went from 131 to 135.
- 2026-09-07 —
  [applicative-derived-probing](../tmp/plan/step-applicative-derived-probing.md)
  converted `Applicative`'s five derived members — `map`, `lift`,
  `zip_with`, `discard_first`, `discard_second` — to the probe-then-derive
  shape, all one-way (`Applicative` has no mutually-derivable pair besides
  `invoke`/`ap`, already converted). This is the first conversion to reach a
  wording-generating header: the `\effects-equiv` markup on all five, which
  renders the body, had to become explicit `\constraints`/`\effects`/
  `\returns` prose in the shape `ap` already uses, since a probing body is
  not specification text. `papers/wording/transpose.applicative.derived.md`
  and `transpose.applicative.syn.md` were regenerated and copied over; the
  five pre-existing drifted fragments (`transpose.errset.obs.md`,
  `transpose.errset.recover.md`, `transpose.errset.syn.md`,
  `transpose.expected.syn.md`, `transpose.grade.syn.md` — one more than this
  step's own file expected, `errset.obs.md` having drifted since) were left
  untouched. `discard_first` and `discard_second` needed a second alternative
  that names a callable, and a lambda-expression cannot be spelled
  identically at both an in-class declaration and its out-of-line
  definition — each occurrence is a distinct, unrelated closure type, so the
  two declarations stop matching. `apply.hpp` gained two small named
  evaluator objects, `discard_first_eval` and `discard_second_eval`, in a
  `\omit`ted nested `detail` namespace, the same role `applicative_eval`
  already plays for `ap`. Traversable's derived members (`for_each`,
  `transpose`, `traverse_with`, `transpose_with`) were deliberately left
  unconverted per this step's file: two are delegation to a caller-supplied
  object rather than derivations over `Impl`, and `traverse.hpp` carries a
  DELIBERATE CONSTRAINT comment that makes widening it a decision rather
  than a chore. Suite went from 135 to 146 (11 added, all in
  `apply.test.cpp`: preference and fallback tests for `map`, `zip_with`,
  `lift`, `discard_first`, `discard_second`, plus one per-instantiation test
  for `map`).
- 2026-09-07 —
  [foldable-derived-probing](../tmp/plan/step-foldable-derived-probing.md)
  converted `Foldable`'s whole surface — `fold_map`/`fold_right` (the third
  mutually-derivable pair) plus the nine one-way derived members (`length`,
  `fold_left`, `combine_all`, `fold`, `any_of`, `all_of`, `empty`,
  `to_vector`, `find_first`) — to the probe-then-derive shape, closing the
  latent `fold_map`/`fold_right` mutual-recursion hazard structurally:
  before this step, a `Map` that omitted a `using`-declaration for one side
  of the pair sent the two derivations into unbounded mutual template
  recursion (each round nesting another `RightFoldProgram`); both
  derivations now address `Impl` directly (`impl_of(self)`), so neither can
  re-enter the other through `self`, and an `Impl` with neither basis fails
  as a clean constraint (its `fold_map`/`fold_right` members do not exist,
  verified with a `has_fold_map` concept the way the library's other
  "does not exist" cases are tested), with a `static_assert` naming both
  acceptable bases as a last-resort message that is unreachable given the
  declaration-level constraint already did the work. `VectorFoldableImpl`
  gained a native `length` (`values.size()`) with **no** edit to
  `VectorFoldableMap` — the ergonomics demonstration this step exists to
  make. One correction to the one-way members' shape, found empirically: the
  seven members deriving directly from `fold_map` (`length`, `fold_left`,
  `combine_all`, `any_of`, `all_of`, `to_vector`, `find_first`) must probe
  `self.fold_map(...)` in their second alternative, not `impl.fold_map(...)`
  — since `fold_map` is now itself conditionally available via either basis,
  the Impl-level shallow check the rest of the codebase uses for one-way
  derivations (`map`, `zip_with`, ... in `apply.hpp`) wrongly excludes an
  `Impl` that only provides `fold_right` + `element_type`; a hazard-Impl test
  calling `to_vector` caught this directly (compiled-away member, not a
  runtime failure). `fold`/`empty`, which derive from `combine_all`/`any_of`
  rather than `fold_map` directly, already needed this `self`-routed shape
  per this step's own file. Two lambda-related GCC/Clang portability notes
  worth carrying forward: a lambda that captures a declaration-level
  parameter (`function`, `predicate`) inside a trailing requires-clause
  fails under GCC (`-Wtemplate-body`, "use of parameter outside function
  body"), and a lambda that captures a local variable inside a `requires{}`
  used in a `static_assert` body fails under the Clang front end the wording
  generator uses ("variable cannot be implicitly captured" / "reference to
  local variable declared in enclosing function") even though GCC accepts
  it; both are fixed the same way, with a non-capturing marker lambda whose
  return-type shape is all the probe needs. `fold.hpp` is not
  wording-generating and stayed that way; `sequence.hpp`'s new native
  `length` is `\omit`ted, confirmed by regenerating and diffing wording —
  only the five pre-existing drifted fragments appear, nothing under
  `transpose.range.*`. Suite went from 146 to 151 (5 added: a native-`length`
  preference test, a per-instantiation `to_vector` test, the hazard test
  exercising a `fold_right` + `element_type` `Impl` through a `Map` with no
  `using`-declaration at all, the `has_fold_map` non-existence test, plus one
  more assertion added to the existing `sequence.hpp` `length` test for
  empty/one-element vectors).
- 2026-09-07 —
  [applicative-ap-only-probing](../tmp/plan/step-applicative-ap-only-probing.md)
  found bullet 2 above stated too broadly for a dual-basis class: `map`,
  `zip_with`, `discard_first` and `discard_second`'s second alternative,
  written by
  [applicative-derived-probing](../tmp/plan/step-applicative-derived-probing.md),
  probed `impl.invoke(...)` while their bodies derive through
  `self.invoke(...)`. For an ap-only `Impl` (`pure` + `ap`, no native
  `invoke`) the body still compiles, through the base's own synthesized
  `invoke`, but the Impl-directed clause is false, so the member silently
  vanished from overload resolution — a regression against the commit
  before that step, invisible because no in-tree `Impl` is ap-only. `lift`
  was unaffected: its second alternative names `pure`, a hard `Impl`
  requirement, so `impl.pure` and `self.pure` cannot disagree. The four
  members' second alternatives were readdressed to `self.invoke(...)`;
  `lift` converted to `self.pure(...)` too, not because it was broken, but
  so clause and body agree everywhere rather than carrying one documented
  exception. `ap` itself is untouched — `invoke`/`ap` is the
  mutually-derivable pair, and both of its alternatives correctly address
  `Impl` directly, which is what closes the derivation cycle.
  `Monad::fmap`'s Impl-directed derivation is a licensed exception distinct
  from both patterns: it is reached only through a wrapping
  `Functor<SomeMonadMap>`, where `self` is the outer `Functor` and the
  inner base's own surface is `protected` and unreachable, so
  `self`-routing is not an option there, and `bind`/`pure` are hard
  requirements, so nothing can vanish. The rider that matters downstream: a
  self-routed probe is only as strong as the constraint on the member it
  names — `self.fold_map(...)` is strong because `Foldable::fold_map` is
  itself constrained, while `self.invoke(...)` is weak, because
  `Applicative<Impl>::invoke` carries no `requires`-clause at all and
  reports a missing basis only through its own body's `static_assert`, by
  design, the GHC-`MINIMAL` message. The four converted members' second
  alternatives are therefore vacuously satisfied for a `Map` with no
  `using Impl::invoke;` re-export — correct, since the class invariant
  already guarantees a complete basis, but no later step may treat those
  clauses as proof that `Impl` itself has one; the strong check belongs on
  `applicative_impl`, over `Impl` directly. Left open: constraining
  `Applicative::invoke` itself would make the probe strong, and was
  deliberately not done here — its ap-derivation runs through
  `detail::terminating_partial` currying and has no spellable
  single-expression probe, which is a design change to a published basis
  member, not a defect fix. `papers/wording/transpose.applicative.derived.md`
  and `transpose.applicative.syn.md` were regenerated and copied over,
  alongside the five pre-existing drifted fragments
  (`transpose.errset.obs.md`, `transpose.errset.recover.md`,
  `transpose.errset.syn.md`, `transpose.expected.syn.md`,
  `transpose.grade.syn.md`), left untouched. Suite went from 151 to 153 (2
  added: an ap-only `Impl`/`Map` exercising the whole derived surface, and
  a `has_map`/`has_zip_with` concept pair proving an inapplicable callable
  still makes `map`/`zip_with` disappear rather than hard-error against the
  shipped invoke-basis object).
