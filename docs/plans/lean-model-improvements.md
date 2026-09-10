# Plan: strengthen the Lean model of C++ graded effects

## Status

Proposed follow-up to the completed graded Transpose model. The verified
baseline is Lean 4.34.0-rc2, 745 build jobs, 203 inventoried theorems, no
flagged laws, and no `sorry`, `admit`, `native_decide`, or project axioms.

This plan addresses correctness defects in the current description, then
extends the model from a tag-only `expected` analogue into a reusable model
of payload-bearing graded effects and genuinely applicative-polymorphic
traversal. The existing concrete development remains the regression oracle
throughout the work.

## Executive summary

The current development is strong at the algebra it actually formalizes:

- `Grade Err := Finset Err` accurately models finite sets of error kinds.
- `widen` is coherent and proof-irrelevant.
- exact-union and sufficient-grade operations are connected by explicit
  bridges.
- monad-derived short-circuiting and accumulating applicatives are correctly
  distinguished.
- the counterexamples around evaluation order and flattening are valuable and
  should remain permanent regression tests.

The main limitation is one of scope. The model currently represents an error
kind as the entire error value, specializes traversal to one carrier, and
abstracts the grade algebra without abstracting the carrier operations that
consume it. Some prose consequently claims more than the corresponding
theorem establishes.

The target design has four layers:

1. a precisely named grade algebra;
2. cast-free, sufficient-grade operational interfaces;
3. payload-bearing concrete short-circuiting and accumulating carriers;
4. a container traversal interface polymorphic over graded applicatives.

Exact-union operations remain derived conveniences, and the current model is
retained as the unit-payload specialization.

## Problems to address

### 1. `Pomonoid` is documented as a partial order but defines a preorder

`Graded/Obligations.lean` gives `Pomonoid.le` reflexivity and transitivity but
does not require antisymmetry. Calling this a partial order is incorrect, and
it obscures the role antisymmetry would play in deriving idempotence from
least-upper-bound laws.

This should not be fixed merely by adding an unused field to every operational
hypothesis. The proofs demonstrate that sequencing needs only a preorder. The
abstraction should say so.

### 2. Fold equality is confused with semantic reachability

`foldGrade_cons_ne_nil` proves that folding a repeated annotation `g` over a
nonempty list returns `g`. It does not prove that every kind in `g` can be
produced by the element function. For example, an always-successful function
can have result type `Graded {E.parse} Nat`, while `E.parse` is unreachable.

The existing theorem is useful, but it is an annotation-normalization theorem,
not a completeness theorem about behavior.

### 3. Error kinds have no payloads

The current constructor

```lean
err : (e : Err) -> e ∈ g -> Graded g alpha
```

treats the kind as the value. A C++ `error_set<Es...>` selects an error type,
but an instance normally stores a value of that type. The model therefore
cannot state preservation laws for parse locations, diagnostics, error codes,
or other per-alternative data.

### 4. `traverse` is specialized rather than a traversable abstraction

The current traversal is specifically `List` through the short-circuiting
`Graded` carrier. It proves useful list facts and a composition theorem, but it
does not quantify over graded applicatives or transformations between them.
In particular, the accumulating carrier is never traversed, even though
collecting independent failures is the canonical applicative traversal use
case.

### 5. The generic grade algebra is disconnected from carrier operations

`Obligations.lean` has abstract grades, including the `Nat` counterexample,
while `Graded`, `bind`, `ap`, and `traverse` remain specialized to
`Finset Err`. Thus statements about what arbitrary grades require are
supported by a property inventory and grade-only witnesses, not by a generic
carrier-level theorem.

### 6. Canonical representation is not C++ type identity

`canonEquiv : Grade Err ≃ Canon Err` proves a semantic equivalence between
two Lean representations. `canon_perm` proves that permutations normalize to
equal canonical values. Neither theorem establishes C++ alias identity,
mangling stability, ABI properties, or correct normalization across
translation units.

The Lean results are correct; the prose and acceptance boundary should call
them representation theorems rather than proofs of C++ type identity.

### 7. The two morphism records do not share a complete bridge

`GradedHom` preserves exact joins and bottom, while `GradedHomK` requires only
monotonicity and sufficient-grade operational laws. A `GradedHom` grade map is
monotone, but the carrier record lacks enough information to derive a full
`GradedHomK`:

- it does not say that `hom` commutes with `widen`;
- it does not expose one payload-independent mapping of error alternatives.

Concrete renaming has both properties, but the interfaces do not name them.

### 8. The documented test policy is not mechanically enforced

The law inventory is comprehensive, but the corresponding `Tests/*.lean`
files do not explicitly reference every theorem. A name-reference audit finds
dozens of omissions. Some present examples also instantiate only reflexive
casts or homogeneous one-element tuples, so they do not exercise the feature
the theorem exists to demonstrate.

### 9. Module boundaries now hide dependency costs

`Graded/Sufficient.lean` contains the sufficient-grade monad, applicative,
traversal, composition, and morphism layers in one file. Importing `bindK`
therefore imports substantially more of the model than its definition needs.
`Canonical.lean` imports tuple sequencing only to reuse a grade fold theorem.

## Target design

### Grade algebra

Separate the operational preorder from stronger, optional properties. A
representative interface is:

```lean
class PreorderedGradeMonoid (G : Type u) where
  join : G -> G -> G
  bot : G
  le : G -> G -> Prop
  join_assoc : forall a b c, join (join a b) c = join a (join b c)
  bot_join : forall a, join bot a = a
  join_bot : forall a, join a bot = a
  le_refl : forall a, le a a
  le_trans : forall {a b c}, le a b -> le b c -> le a c
  bot_le : forall a, le bot a
  join_mono : forall {a b c d}, le a b -> le c d ->
    le (join a c) (join b d)

class IsPartialOrderGrade (G : Type u) [PreorderedGradeMonoid G] : Prop where
  le_antisymm : forall {a b},
    PreorderedGradeMonoid.le a b -> PreorderedGradeMonoid.le b a -> a = b

class IsCommGrade (G : Type u) [PreorderedGradeMonoid G] : Prop where
  join_comm : forall a b, join a b = join b a

class IsIdemGrade (G : Type u) [PreorderedGradeMonoid G] : Prop where
  join_idem : forall a, join a a = a
```

The exact names may be shortened, but two constraints are important:

- operational theorems must not acquire antisymmetry merely to preserve the
  old word "partial";
- mixins should take the base instance as a parameter rather than duplicating
  it through an inheritance diamond.

Add a separate least-upper-bound mixin containing `le_join_left`,
`le_join_right`, and `join_le`. With antisymmetry it should prove idempotence;
with only the preorder it should prove equivalence in both directions rather
than equality. This resolves the current open `grade-join-strength` question
at the type level without forcing one answer on every consumer.

### Operational interfaces: sufficient grade first

The sufficient-grade layer should become the primary abstract API because its
laws compare terms in the same type and do not hide transports. One possible
shape is:

```lean
class GradedFunctorK (G : Type u) (M : G -> Type v -> Type w)
    [PreorderedGradeMonoid G] where
  map : {g : G} -> {alpha beta : Type v} ->
    (alpha -> beta) -> M g alpha -> M g beta
  widen : {g k : G} -> {alpha : Type v} ->
    le g k -> M g alpha -> M k alpha

class GradedMonadK (G : Type u) (M : G -> Type v -> Type w)
    [PreorderedGradeMonoid G] extends GradedFunctorK G M where
  pure : {alpha : Type v} -> alpha -> M bot alpha
  bindK : {g h k : G} -> {alpha beta : Type v} ->
    le g k -> le h k -> M g alpha ->
    (alpha -> M h beta) -> M k beta

class GradedApplicativeK (G : Type u) (F : G -> Type v -> Type w)
    [PreorderedGradeMonoid G] extends GradedFunctorK G F where
  pure : {alpha : Type v} -> alpha -> F bot alpha
  apK : {g h k : G} -> {alpha beta : Type v} ->
    le g k -> le h k -> F g (alpha -> beta) -> F h alpha -> F k beta
```

Put laws in separate `Lawful...` classes. Keep the current theorem style for
the concrete instances so the generated C++ inventory remains readable.
Define `pureK` once, outside both classes, as `widen (bot_le k) (pure a)`.
Leaving a separate primitive `pureK` at every grade would permit its behavior
to depend on the nominated grade and would require an avoidable coherence law.

Derive exact-union conveniences using the two join inclusions:

```lean
def bind (x : M g alpha) (f : alpha -> M h beta) : M (join g h) beta :=
  bindK (le_join_left g h) (le_join_right g h) x f
```

The current `bind_eq_bindK`, `ap_eq_apK`, `traverse_eq_traverseK`, and
`flatten_eq_flattenK` then become compatibility theorems between the legacy
definitions and these derived operations. Once migration is complete, they
can be reduced to definitional equalities or retained as named API promises.

Do not derive every applicative from a monad. The accumulating applicative is
a first-class `GradedApplicativeK` instance with no `GradedMonadK` instance.
The existing `Accum.notMonad` theorem remains the reason.

### Payload-bearing error signature

Introduce an error signature independently of the grade representation:

```lean
structure ErrorSignature where
  Kind : Type u
  Payload : Kind -> Type v
```

For the `Finset` grade instance:

```lean
abbrev ErrorGrade (S : ErrorSignature) [DecidableEq S.Kind] := Finset S.Kind

inductive ExpectedG (S : ErrorSignature) [DecidableEq S.Kind]
    (g : ErrorGrade S) (alpha : Type w)
  | ok : alpha -> ExpectedG S g alpha
  | err : (k : S.Kind) -> S.Payload k -> k ∈ g -> ExpectedG S g alpha
```

Provide a tag-only specialization with `Payload := fun _ => PUnit`, and prove
an equivalence to the current `Graded`. This allows all existing examples and
counterexamples to remain available while new examples carry realistic data.

For accumulation, store a nonempty ordered list of dependent errors:

```lean
Sigma S.Payload
```

Each element carries a proof that its projected kind belongs to `g`. Preserve
list order because the short-circuit projection deliberately selects the first
error. If unordered accumulation is later desired, add a separate quotient or
multiset carrier rather than silently changing this observable contract.

### Grade-generic carriers

The operational interfaces above allow arbitrary carriers without requiring
all grades to be sets. For an expected-style carrier over an arbitrary grade,
add an admission relation:

```lean
class ErrorAdmission (S : ErrorSignature) (G : Type x)
    [PreorderedGradeMonoid G] where
  Admits : S.Kind -> G -> Prop
  bot_forbids : forall k, not (Admits k bot)
  mono : forall {g h : G} {k : S.Kind},
    le g h -> Admits k g -> Admits k h
```

Instantiate this with membership for `Finset S.Kind`. A counting grade may use
a different carrier and admission relation, or only instantiate the abstract
operational interfaces. This avoids pretending every useful grade is a set of
error alternatives. Admission into `join g h` is derived from `mono` and the
two join inclusions rather than duplicated as primitive fields.

### Traversable abstraction

Define list traversal once in terms of `GradedApplicativeK`. The nominated
result grade eliminates the repeated-grade fold from the operation:

```lean
def List.traverseGK [GradedApplicativeK G F]
    (hg : le g k) (f : alpha -> F g beta) : List alpha -> F k (List beta)
```

Then instantiate it for:

- short-circuiting `ExpectedG`;
- accumulating `AccumG`;
- composed applicatives.

Prove the usual laws at the polymorphic layer:

- identity;
- composition without flattening the two effects;
- naturality under a graded applicative transformation;
- source `map` fusion.

Keep shape preservation as a separate law of the `List` traversal, not a law
of every traversable container.

Add behavior specifications distinct from grade annotation facts:

```lean
def CompleteGrade (f : alpha -> ExpectedG S g beta) : Prop :=
  forall k, k ∈ g ->
    exists (a : alpha) (payload : S.Payload k) (hk : k ∈ g),
      f a = ExpectedG.err k payload hk
```

The carrier already gives soundness: emitted errors belong to the grade.
Completeness is optional and generally false. Prove that if `f` is complete,
then traversal as a function over all lists is complete by using singleton
lists. Do not attach this condition to ordinary traversal laws.

For accumulating traversal, specify and test:

- errors occur in source-list order;
- every failing position contributes its error list;
- `toExpectedG` selecting the first error commutes with traversal into the
  short-circuiting carrier;
- success returns `List.map` of the successful payload function.

### Morphisms and transformations

Factor grade and carrier mappings into reusable components:

```lean
structure MonotoneGradeMap (G H : Type) where
  map : G -> H
  mono : forall {a b : G}, le a b -> le (map a) (map b)

structure ErrorSignatureMap (S T : ErrorSignature) where
  kind : S.Kind -> T.Kind
  payload : forall k, S.Payload k -> T.Payload (kind k)
```

A carrier transformation should explicitly state:

- naturality in the success payload;
- commutation with `widen`;
- preservation of `pureK` and `bindK` or `apK`;
- one payload-independent `ErrorSignatureMap` for error alternatives.

Define exact-grade homomorphisms as the sufficient-grade transformation plus
`map_bot` and `map_join`. This yields a general forward conversion to the
sufficient-grade record. The reverse conversion remains unavailable without
the two algebraic preservation laws, as the existing constant-map
counterexample demonstrates.

Use the same transformation interface to state traversable naturality. Error
renaming, accumulation-to-first-error, and representation changes then become
instances rather than unrelated theorem families.

### Canonical representation and the C++ boundary

Keep `Canon`, `canonEquiv`, and `canon_perm`, but revise their stated contract:

- Lean proves that the sorted representation and `Finset` carry the same
  mathematical grade;
- the `LinearOrder` requirement documents the extra datum required by a sorted
  normal form;
- Lean does not prove that a particular C++ metaprogram implements the normal
  form or gives stable type identity.

Complete the boundary with compile-time C++ probes generated or transcribed
from `docs/probe-harness.md`:

```cpp
static_assert(std::same_as<error_set<A, B>, error_set<B, A>>);
static_assert(std::same_as<error_set<A, A, B>, error_set<A, B>>);
static_assert(std::same_as<join_t<error_set<A>, error_set<B>>,
                           error_set<A, B>>);
```

Add probes in more than one translation unit and, where ABI is a stated
promise, inspect or compare mangled names on supported toolchains. The C++
tests own type identity; the Lean model owns the normal-form mathematics.

### Test and audit enforcement

Extend `scripts/laws-inventory.py` or add a companion script that checks an
explicit marker for every theorem, for example:

```lean
-- TESTS: Graded.bind_assoc
example ... := Graded.bind_assoc ...
```

Allow exemptions only through a reviewed JSON file containing a reason. Do
not infer coverage merely from imports or theorem-name substrings in prose.

Add fixture requirements for tests of transport and heterogeneity:

- associative casts use three distinct nonempty grades;
- commutativity tests use distinct nonempty grades on both sides;
- heterogeneous tuple tests contain at least two distinct payload types and
  two distinct grades;
- morphism cast tests use a nontrivial equality, not `g = g`;
- both-error tests use distinguishable kinds and payloads;
- accumulating traversal tests include zero, one, and multiple failures.

Add these acceptance commands:

```text
make verify       # full Lean build
make nosorry      # forbidden proof escapes
make laws         # law inventory is current
make test-coverage
make axioms       # selected public theorems contain no sorryAx/project axiom
make cpp-probes   # when the C++ implementation is available
```

Run them in CI against the pinned Lean and Mathlib revisions. Cache `.lake`
artifacts, but test a cold dependency resolution periodically so the lockfile
is known to be sufficient.

### Module layout

Split the additive layers without changing public imports immediately:

```text
Graded/Algebra/Preordered.lean
Graded/Algebra/Finset.lean
Graded/Effect/FunctorK.lean
Graded/Effect/MonadK.lean
Graded/Effect/ApplicativeK.lean
Graded/Effect/Transformation.lean
Graded/Expected/Payload.lean
Graded/Expected/ShortCircuit.lean
Graded/Expected/Accum.lean
Graded/Traversable/List.lean
Graded/Traversable/Compose.lean
Graded/Representation/Canon.lean
```

Keep `Graded/Sufficient.lean`, `Graded/Canonical.lean`, and other current
entry points as re-export shims during migration. Extract `joinAll` into a
grade-fold module so canonicalization does not depend on heterogeneous tuple
sequencing.

## Implementation sequence

### Phase 0: correct the specification and lock the baseline

1. Replace the inaccurate partial-order description with preorder terminology.
2. Correct all reachability and type-identity overclaims.
3. Fix stale descriptions of the obligation hierarchy.
4. Add CI and `make test-coverage` scaffolding.
5. Record the current 203 theorems as the compatibility baseline.

Acceptance:

- all existing theorems still build;
- every existing theorem has a test marker or justified exemption;
- generated law files and the working tree are clean after `make all`.

### Phase 1: introduce the grade and operational abstractions

1. Add `PreorderedGradeMonoid` and independent stronger mixins.
2. Instantiate them for `Grade Err` and `Nat`.
3. Add `GradedFunctorK`, `GradedMonadK`, and `GradedApplicativeK` with lawful
   companions.
4. Instantiate the existing `Graded` and `Accum` operations.
5. Derive exact-union operations and prove compatibility with the legacy API.

Acceptance:

- generic monad/applicative laws mention no `Finset`;
- sufficient-grade law statements contain no `cast`;
- the accumulating instance has no monad instance;
- the existing counterexamples still compute identically.

### Phase 2: add payload-bearing carriers

1. Add `ErrorSignature`, `ExpectedG`, and payload-bearing accumulation.
2. Prove `map`, `widen`, monad, applicative, and sufficient-grade laws.
3. Add the unit-payload equivalence to legacy `Graded`.
4. Port validation examples to payload-bearing parse/range/I/O errors while
   retaining tag-only examples as compatibility tests.

Acceptance:

- error payloads are preserved by `map`, `widen`, `bindK`, and `apK`;
- many-to-one kind maps have explicit payload conversion functions;
- the unit-payload specialization recovers legacy results.

### Phase 3: generalize traversal and add accumulation

1. Define list traversal from `GradedApplicativeK`.
2. Instantiate short-circuiting, accumulating, and composed effects.
3. Prove identity, composition, naturality, map fusion, and list shape.
4. State annotation normalization separately from optional grade completeness.
5. Prove first-error projection commutes with accumulating traversal.

Acceptance:

- the traversal definition contains no reference to a concrete carrier;
- accumulating traversal reports all failures in source order;
- flattened composition remains conditional where the existing counterexample
  requires it;
- no law calls annotation equality semantic reachability.

### Phase 4: unify morphisms

1. Add monotone grade maps, error-signature maps, and applicative
   transformations.
2. Make `hom_widen` and payload-independent error mapping explicit.
3. Derive the full exact-to-sufficient morphism conversion.
4. Re-express renaming and accumulation projection through the shared API.

Acceptance:

- `renameHomK` factors through the general conversion;
- traversal naturality is an instance of the generic transformation law;
- the existing no-converse counterexample remains valid.

### Phase 5: validate representation claims in C++

1. Reword the Lean canonicalization contract.
2. Add C++ same-type and operation probes.
3. Run probes across supported compilers and multiple translation units.
4. Document the ordering and ABI assumptions of the actual canonicalizer.

Acceptance:

- every C++ type-identity claim has a `static_assert`;
- every semantic equation in the probe harness either passes or is documented
  as intentionally conditional;
- the Lean report makes no ABI or type-identity claim unsupported by C++
  evidence.

### Phase 6: modularize and deprecate legacy internals

1. Split `Sufficient.lean` and extract grade folds.
2. Retain compatibility re-exports for one migration window.
3. Migrate examples and documentation to the new primary interfaces.
4. Remove only definitions whose replacement has a proved bridge and complete
   test coverage.

Acceptance:

- importing monad operations does not import traversal, composition, or
  morphism implementations;
- no public theorem disappears without a compatibility alias or documented
  migration;
- the final law inventory distinguishes generic, concrete, representation,
  and C++-probe obligations.

## Risks and controls

### Universe and typeclass complexity

Indexed constructors and payload families will expose universe constraints
that the concrete model currently avoids. Introduce the abstract interfaces
in small modules, keep universe parameters explicit, and add compile-only
examples at two different universe levels.

### Instance diamonds

Independent commutative, idempotent, partial-order, and least-upper-bound
mixins can create multiple routes to the base algebra. Make mixins `Prop`
classes parameterized by one existing base instance. Do not let each mixin
inherit and recreate the base data.

### Law duplication during migration

The legacy and generic layers will temporarily express the same laws. Require
each concrete legacy theorem either to invoke a generic theorem or to be
listed as an intentionally independent C++-facing restatement. The inventory
should record this relationship.

### Accumulation order becoming accidental

The first-error projection makes list order observable. Treat left-to-right
ordering as part of the contract and test it. An unordered bag should be a
separate carrier with a separate projection policy.

### Confusing semantic proof with C++ implementation evidence

Keep the boundary explicit: Lean proves algebra and functional behavior;
C++ compile tests prove template identity and overload behavior; ABI checks
prove only the platforms on which they run.

## Definition of done

The follow-up is complete when:

- the grade algebra uses accurate preorder/partial-order terminology;
- no theorem or documentation confuses an annotation with behavioral
  reachability;
- the primary expected-style carrier stores typed error payloads;
- monad and applicative laws are proved over abstract sufficient-grade
  interfaces;
- list traversal is polymorphic over graded applicatives and is exercised by
  both short-circuiting and accumulating instances;
- morphisms commute with widening and carry errors through an explicit
  signature map;
- representation equivalence and C++ type identity are stated and tested in
  their proper layers;
- every inventoried theorem has mechanically checked test coverage or a
  reviewed exemption;
- `make verify`, `make nosorry`, `make laws`, `make test-coverage`, and the C++
  probes are green in CI.
