# Migration review — the sufficient-grade layer

Scoped `model: opus` consult, 2026-09-08, on `main` at `3ffe804`, bounded
to checklist steps 19–24 (the three-leg sufficient-grade migration).
Steps 1–18 were reviewed by [INTEGRATION-REVIEW.md](INTEGRATION-REVIEW.md)
and are not re-reviewed here. Boot: the orchestrator's brief (this file,
replaced below), `handoff-migration-review.md`, and the tree.

**Verified state.** `make all` re-run in this session: exit 0. `lake build`
green (737 jobs), `nosorry: clean`, `check-letters.sh` silent,
`laws-inventory: 203 theorems tabulated, 0 flagged`, `git diff --exit-code`
on the generated docs clean, working tree clean.

Stronger than `make nosorry`, which is a grep: `#print axioms` on sixteen
of the migration's own declarations — all four bridges, `apK_flip`,
`flattenK_comm`, `flatten_apK`, `traverseCompK_eq`, `traverseK_length`,
`bindK_assoc`, `apK_comp`, `Comp.apK_interchange`,
`GradedHom.gmap_mono`, `constHomK_not_gmap_bot`, and the two instances
`renameHomK`/`constHomK` — reports `[propext, Classical.choice,
Quot.sound]` for every one and nothing else. No `sorryAx`, no project
axiom anywhere in the new closure. `docs/allowed-axioms.md` stays
honestly empty.

**Scope confirmed, not assumed.** `git diff --name-only 2c2e4dd..HEAD --
Graded/` is exactly `Graded/Obligations.lean` and `Graded/Sufficient.lean`.
Every other operational module is byte-identical across all six steps.
Two files outside `Graded/` that the check as written does not see:
`Graded.lean` and `Tests.lean` each gained one `import` line. They are
import manifests, not modules; the stronger claim holds.

**Counts in this review were taken from the source and from
`docs/laws.json`, never from another sentence.** Statements were
extracted by cutting each declaration at the first depth-0 `:=` *or* at
the first `|` of an equation-style proof — the second case is the one the
earlier 39-vs-38 scanner missed, and it is still costing the repo a wrong
number (§4).

---

## 1. Findings for the C++ side

Read first. Each names the theorem that establishes it and the letter that
explains it to a C++ reader. "P3200" is the transpose paper.

### 1.1 The laws need `error_set` *subsumption*, not `error_set` *union*

`#cpp-counterpart` already records that `Es ⊆ Es'` is an implicit
conversion of the carrier. This migration's finding is that the implicit
conversion is the **only** thing the laws need. Every monad, applicative,
traversal, flatten and composite law restates against a caller-nominated
`E` with `Es_f ⊆ E` and `Es_g ⊆ E` in place of the computed
`error_set<Es_f..., Es_g...>`, and all 57 of them
(`Graded/Sufficient.lean`) hold with **no transport at all** — verified
independently here, 0 of 57 statements contain a `cast`, against 38 of the
146 union-graded ones.

Nothing is lost by saying it that way: `bind_eq_bindK`, `ap_eq_apK`,
`traverse_eq_traverseK` and `flatten_eq_flattenK` instantiate the
nominated form at the exact union and recover the union-graded operation,
`rfl` in every constructor case.

**For P3200**: state the monad/applicative laws in the subsumption form.
It removes every "up to canonicalization" caveat from the wording, and
costs one sentence saying the exact-union spelling is the special case.
**Letters 17, 18, 20, 22.**

### 1.2 Commutativity of `error_set` is a type-identity promise, not an operational one

- `Graded.ap_flip` needs `Grade.join_comm` *by construction* (it compares
  `g ⊔ h` against `h ⊔ g`); `apK_flip` needs **no property at all**.
- `flatten_comm` pays `cast (Grade.join_comm h g)`; `flattenK_comm` needs
  no hypothesis and is `rfl` — and not vacuously: `swap`
  (`Graded/Compose.lean:36`) genuinely moves an inner `err` to the top
  level and back, and the theorem says both sides still compute the same
  error.
- `Comp.grade_reassoc` — the last commutativity citation sitting in an
  operational position — has **no analogue**, because `flatten_apK` never
  produces the `cast` it existed to serve.

Confirmed mechanically, not from prose: `laws-inventory.py --by-property`
tags all 57 `Sufficient.lean` theorems either `order` (22) or nothing
(35). Zero `commutative`, zero `idempotent`, zero `associative`, zero
`homomorphism`.

So `error_set<A,B> ≡ error_set<B,A>` earns its keep as a claim about the
*type* — identity, mangling, ABI, the sorted detail carrier — and not as
something `and_then` or `apply` needs to be correct. **Letters 18, 19, 22.**

### 1.3 `traverse`'s length-independence was never in danger; the fold was the cost

`foldGrade` and `foldGrade_cons_ne_nil` — the fold and the idempotence
that makes `traverse`'s C++ signature typeable at a *computed* grade —
have **no analogue at all** in the sufficient-grade layer. Not a cheaper
one: none. `traverseK hg f xs : Graded k (List β)` for every `xs` before
any theorem is stated about it.

The C++ reading is sharper than "traverse needs idempotence". The C++
signature already deduces the result error set from the element function
(`Es_elem`), which *is* the nominated form — `traverse_eq_traverseK`
instantiates at `g` itself. The idempotence obligation was an artifact of
*defining* the traversal by folding the grade, not a requirement of the
signature C++ actually writes. **Letter 20.**

Caveat worth keeping: the exactness claim (that the result set really is
`Es_elem` and not something wider) is what `foldGrade_cons_ne_nil` buys.
Nominating the bound does not prove exactness — it makes exactness the
caller's statement instead of the library's.

### 1.4 Flatten-then-apply and apply-then-flatten disagree, and the migration did not fix it

`flatten_apK` carries `flatten_ap`'s three-way disjunctive hypothesis
**verbatim**. Checked here independently, not taken on trust: in the
excluded shape — `ff`'s outer layer succeeds carrying a failing inner
payload while `xx`'s outer layer also fails — `flattenK ∘ Comp.apK`
reports `xx`'s error and `apK ∘ flattenK` reports `ff`'s inner error.
`Tests/Sufficient.lean:509-542` builds exactly that case at disjoint
grades and `#guard`s the two renderings as `err E.range` and `err E.io`.
The law is conditional, the condition is load-bearing, and it is a
value-level fact that no amount of grade nomination touches.

**For P3200**: if a nested `expected<expected<T, Es2>, Es1>` can be
flattened either before or after `apply`, the paper must say which error
survives, or forbid one order. Same shape as the first review's
leftmost-failure-wins finding, one structure further in. **Letter 22.**

### 1.5 A conversion between two error-set designs needs monotonicity, not a homomorphism

`GradedHomK` (`Graded/Sufficient.lean:915`) asks of the grade map only
`gmap_mono` — `Es ⊆ Es'` implies `φ(Es) ⊆ φ(Es')` — where `GradedHom`
asks `gmap_join` and `gmap_bot`. `constHomK` inhabits the weaker
obligation with a `gmap` that `constHomK_not_gmap_bot` proves cannot be
completed into a `GradedHom` at all, so the weakening admits strictly
more.

§3 below adds what the step could not: `GradedHom` lifts to a **full**
`GradedHomK` given exactly two further facts, both automatic for any real
`transform_error` — the carrier map commutes with the subsumption
conversion, and its action on the error is a relabelling `Err → Err'`
that does not depend on the value type. Verified in Lean.

**For P3200**, which states no morphism concept today: the requirement on
a `transform_error`-style conversion between graded designs is *monotone
on error sets, natural in the implicit conversion, and relabels the error
independently of `T`* — not "distributes over union and preserves the
empty set". **Letter 21.**

### 1.6 `error_set`'s two extra axioms are independent, and neither is operational

`Graded/Obligations.lean` now states `Pomonoid` — the operational
obligation — plus three independent mixins, including
`IsCanonicalPomonoid` (both axioms together), which is the class a real
`error_set` inhabits and `Nat` does not. No theorem in the file takes the
conjunction as a hypothesis.

**For the paper**: the grade concept's *operational* requirement is
"partially ordered monoid". Commutativity and idempotence belong in
`error_set`'s own contract, as what makes its spelling canonical.
**Letter 19.**

### 1.7 What this run does not license

No leg built anything over the abstract `Pomonoid` framework, so nothing
here says a non-lattice grade could support `traverse`. `Nat` still has
no traversal. See §5.

---

## 2. Does the two-layer-and-bridge design hold across all three legs?

**Yes for the operations, with one correction to the shape of the claim
and two caveats a reader should have.**

**Purely additive — confirmed, with one qualification.** All five
structures named in `#cast-burden-migration-scope` gained a cast-free
layer beside the union-graded original: `bindK`; `apK`/`map2K`/
`apFlippedK`/`Comp.apK`; `traverseK`; `GradedHomK`; `flattenK`/
`Comp.pureK`/`Comp.map2K`/`traverseCompK`. Not one union-graded theorem
changed, and every union-graded module except `Obligations.lean` is
byte-identical to its pre-migration state.

The qualification is that `Graded/Obligations.lean` was **restructured,
not extended** — [obligation-layering] deleted the nesting
`IsIdemPomonoid extends IsCommPomonoid` and replaced it with
`IsIdemPomonoid extends Pomonoid` plus a new `IsCanonicalPomonoid`. That
is a breaking change to a public class (anyone writing `[IsIdemPomonoid
G]` and using `join_comm` loses it), authorized by the step's scope and
harmless in-tree — the only consumers outside that file are four
`inferInstance` examples in `Tests/Obligations.lean`. The handoff's "every
leg is additive to one file" is wrong on the file count and right on the
substance; "no *operational* module changed" is the claim that holds.

**Cast-free, and not by hiding a cast.** The concern worth checking is a
statement that is cast-free only because a `cast` moved into a definition.
It did not. No `def` or `structure` in `Graded/Sufficient.lean` mentions
`cast`, and the operation the K-layer threads instead — `widen`
(`Graded/Widen.lean:19`) — is a plain two-case pattern match, not
`Graded.cast`'s `h ▸ x`. The word `cast` occurs in `Sufficient.lean` only
in prose and in three `simp only` sets inside `traverse_eq_traverseK`'s
proof, which is the bridge, on the union-graded side, exactly where the
file's own comment says it is.

**The four bridges are what they look like.** Four `/-- BRIDGE -/` tags,
all in `Sufficient.lean`, all instantiating the K-form at the grade the
union-graded operation already computes, along the same inclusions:
`bind_eq_bindK` and `flatten_eq_flattenK` are `rfl` in every case;
`ap_eq_apK` is `rw` into reduction lemmas that are themselves `rfl`;
`traverse_eq_traverseK` pays `Grade.join_idem` once, via `traverse_cons`,
on the union-graded side only. That last one is honest but worth naming
precisely: the property is spent *transitively*, by delegation to
`traverse_cons`, so the mechanical scan tags the bridge `order`. The
"zero idempotence citations" claim is a claim about the scan; the bridge
does consume `traverse_cons`'s idempotence, and the file says so.

**Two laws that are weaker than they read, both already disclosed.**

- `traverseK_length` is *not* the analogue of `traverse_length`'s
  interesting content. Length-independence is a property of `traverseK`'s
  signature before any theorem exists; what `traverseK_length` proves is
  the narrower shape-preservation fact. The docstring says exactly this.
  A reader skimming the 57 should not count it as the traversal's
  headline law.
- `bindK_irrel`, `traverseK_irrel` and `traverseCompK_irrel` are `rfl`
  because Lean has definitional proof irrelevance on `Prop`. They are the
  theorems `#cast-burden-migration-scope`'s "the threaded `⊆` obligations
  stayed free" verdict rests on, and that verdict is right — but the
  *reason* is a fact about Lean, and it carries nothing across to C++,
  where there are no proof terms to be irrelevant about. The C++-relevant
  half of the claim is the different one: at a concrete grade every
  inclusion closes `by decide`.
- `traverseK_nil_eq_fromEmpty` is `traverseK_nil` restated in the other
  spelling, `rfl`, and the comment above it says so. It is one of the 57.
  Not a defect; worth knowing before anyone quotes 57 as 57 distinct
  facts.

**No vacuous law found.** `flatten_apK`'s hypothesis excludes exactly one
shape and the two sides genuinely differ there (§1.4). `apK_flip`'s
`honeok` is likewise load-bearing — both-`err` is the case where `apK`
keeps the function's error and `apFlippedK` keeps the argument's.
`flattenK_comm` is `rfl` but not trivial, because `swap` really does
rearrange. `traverseCompK_eq` is a genuine induction. `apK_pure_id`,
`apK_interchange`, `apK_comp`, `flattenK_flattenK`, `bindK_assoc` all
quantify over inhabited constructor cases and are proved by case split,
not by an empty-context trick.

**One thing missing rather than wrong**: there is no `apK_irrel` or
`flattenK_irrel` on disk, though `#cast-burden-migration-scope` mentions
"the analogous fact for `apK`/`Comp.apK`" in the same breath as the three
that exist. The prose is careful enough (it says *fact*, not *theorem*),
but a reader will look for them.

**The prose describing the layer is otherwise accurate.** Every quoted
Lean fragment in the four "sufficient-grade layer" subsections was
checked character-for-character against the tree — `bindK_pure_left`,
`bindK_assoc`, the `GradedHomK` structure, and `flatten_apK`'s full
statement including its `hcond` disjunction (verbatim from `flatten_ap`).
`#compose`'s subsection came back with no discrepancy of any kind. So did
every cast column in the three measurement tables. What went wrong went
wrong in counts and attributions (§4, §6), never in the description of
what the code does.

---

## 3. The `GradedHomK` bridge asymmetry: half finding, half gap

The step files read this as a pattern — operations bridge fully, the one
record bridges partially — and treat that as something the migration
discovered. **Half of that is right and should be kept; half of it is a
property of `GradedHom`'s field list and should be retired.**

**Right, and genuinely structural: there is no converse.** `constHomK`
inhabits `GradedHomK` with a `gmap` (`fun _ => g₀`) that
`constHomK_not_gmap_bot` proves refutes `gmap_bot`, so no
`GradedHomK → GradedHom` map exists in general. That is a real fact about
the two obligations, properly witnessed on disk, and it is the reason
`GradedHom.gmap_mono` is correctly left untagged: it is not a bridge in
the sense the other four are.

**Not right: "even the forward direction stops at `gmap_mono`."** That is
not a fact about records versus operations. It is a fact about which
fields `GradedHom` happens to have. Checked in Lean rather than argued —
this is the piece a worker scoped to `Graded/Sufficient.lean` could not
have done, because it requires reasoning about changing `GradedHom`:

```lean
-- compiles clean against Graded.Sufficient
def liftHomK (H : GradedHom Err Err')
    (hw : ∀ {g g' : Grade Err} {α : Type v} (h₁ : g ⊆ g') (x : Graded g α),
        H.hom (widen h₁ x) = widen (GradedHom.gmap_mono H h₁) (H.hom x))
    (emap : Err → Err')
    (hemap : ∀ {g : Grade Err} {e : Err}, e ∈ g → emap e ∈ H.gmap g)
    (herr : ∀ {g : Grade Err} {α : Type v} (e : Err) (he : e ∈ g),
        H.hom (Graded.err e he : Graded g α) = Graded.err (emap e) (hemap he)) :
    GradedHomK Err Err'
```

with every field discharged, and

```lean
def renameHomK' (φ : Err → Err') : GradedHomK Err Err' :=
  liftHomK (renameHom φ) (fun h₁ x => rename_widen φ h₁ x) φ
    (fun he => Grade.mem_rename he) (fun _ _ => rfl)
```

so the existing `renameHomK` is not special: it *factors through* the
general lift. Three things follow.

1. **The forward gap is exactly two facts, and `docs/design.md` named
   one of them.** `hom` commuting with `widen` is the one the step and
   the design doc identified. It is necessary and it is not derivable
   from `hom_bind`/`hom_pure`, because `widen` is a primitive of the
   carrier that neither field mentions. Correct as recorded.

2. **The second fact is the one nobody spotted, and it is the
   interesting one.** `hom_bindK`'s `err` leaf is asked at payload type
   `β` on the left of the equation and at payload type `α` on the right.
   A per-payload-type error action is therefore not enough: the field
   silently requires `hom`'s action on errors to be **natural in the
   payload** — a single relabelling `Err → Err'` used at every `α`. Every
   `hom` anyone can actually write satisfies this (you cannot manufacture
   an `α` out of an `err`), but `GradedHom`'s field list cannot prove it,
   and Lean cannot supply it by parametricity. It is a genuine extra
   obligation, and it is the one that makes `GradedHomK` say something
   about *carriers* rather than only about grades.

3. **A third fact you would expect to need is free.** `hom` preserving
   `ok` follows from `hom_pure` plus (1) — proved above as `homOk` — so
   the lift needs two hypotheses, not three.

**Verdict.** The asymmetry is not a discovered law about structures. What
the migration actually established, stated the way I would keep it, is:

> `GradedHomK` is `GradedHom`'s *data* with the grade obligation weakened
> from join-semilattice homomorphism to monotonicity, and the carrier
> obligation strengthened from "commutes with `bind`/`pure` at the
> computed union" to "commutes with the subsumption conversion, and
> relabels errors independently of the payload type." Neither obligation
> implies the other, which is why neither structure maps into the other
> as it stands — and why the one thing that *does* transfer,
> unconditionally and in one direction only, is `gmap_mono`.

That is a better sentence than "records bridge differently from
operations", it is falsifiable, and it survives someone later adding the
two fields — which would then make `GradedHom → GradedHomK` total and
`renameHomK` derived rather than restated. **Recommended**: keep
`GradedHom.gmap_mono` untagged; replace the "bridging structures is not
bridging operations" framing in `#morphisms`'s sufficient-grade
subsection and in `#cast-burden-migration-scope`'s log with the field-list
account above; and record the payload-naturality obligation by name,
since it is the part of `GradedHomK` that is doing real work and is
currently invisible in the prose.

---

## 4. `#cast-burden-migration-scope`'s summary table: one arithmetic error, one wrong constant

Re-derived from source, not from the table. Per-module theorem counts
agree exactly with `docs/laws.json`; casts-in-statement counted with a
scanner that handles equation-style proofs.

| module | table says | source says |
|---|---|---|
| `Monad` | 7/8 | 7/8 ✓ |
| `Applicative` | 5/11 | 5/11 ✓ |
| `ComposeApp` | 6/13 | 6/13 ✓ |
| `Traverse` | **2/12** | **1/12** ✗ |
| `Compose` | 4/8 | 4/8 ✓ |
| `Morphism` | 5/15 | 5/15 ✓ |
| `Carrier` | 2/5 | 2/5 ✓ |
| `Widen` | 1/6 | 1/6 ✓ |
| `Accum` | 7/16 | 7/16 ✓ |
| `Ungraded` | 0/16 | 0/16 ✓ |
| `Sufficient` | 57 theorems, 0 casts | 57, 0 ✓ |

**The one error, and it is the fossil of the scanner bug `581da13` was
supposed to have removed.** `Graded/Traverse.lean` has exactly one
theorem with a `cast` in its statement — `traverse_cons`. The table says
two. The rows as printed sum to **39**; the corrected total, which
`docs/design.md:164` already states, is **38**. Correcting `Traverse` to
`1/12` makes the column sum to 38 and reconciles the table with the tree:
110 theorems in the table's ten modules plus 36 in the five it omits
(`Grade` 0/13, `Canonical` 0/5, `Obligations` 0/11, `Tuple` 0/7,
`Prelude` 0/0) is 146, with 38 casts.

Where the phantom came from, for the record: `foldGrade_cons_ne_nil`
(`Traverse.lean:97`) is equation-style, so it has no depth-0 `:=`. A
scanner that cuts a statement at `:=` runs it past the equations and into
the *next declaration's docstring*, which at `Traverse.lean:109` contains
the words "rather than via `cast` along `foldGrade_cons_ne_nil`". The
table is the last place in the repo still carrying that count.

**A separate wrong constant, repeated six times.** "`Comp.ap_interchange`
alone carried 6 casts" — `docs/design.md:363` (the monad section's own
measurement table), `:370`, `:560`, `:2434` (this table's `Comp.ap` row),
`blog/letters/sufficient-grade-applicative.org:25`, and
`tmp/plan/checklist.md`'s step-20 line ("`Comp.ap_interchange`'s six-cast
analogue"). Its
statement contains **two** `Comp.castGH` calls, and `Comp.castGH`
(`ComposeApp.lean:85`) is `Graded.cast eg (Graded.map (Graded.cast eh) x)`
— two `Graded.cast`s each. **Four**, not six. `docs/design.md:560` states
the correct decomposition in a parenthesis immediately after the wrong
number. The *claim* survives the correction: at four it is still the
model's maximum, with `cast_cast` at three and everything else at two or
fewer, so "the single largest per-theorem reduction in the model" stands.

**One row that cannot be summed as written.** The `Comp`/`traverseComp`
row's cast cell reads "(see `Comp.ap` row; `traverseComp_eq`/`flatten_ap`/
`Comp.grade_reassoc` add 2 more casts)". They do not add: `ComposeApp`'s
6/13 already includes `Comp.traverseComp_cons` and `flatten_ap`, and
`Comp.grade_reassoc` has no cast in its statement at all (it is a pure
grade equation). Read literally the row invites 8 for a module that has 6.
Suggest "— included in the `Comp.ap` row's 6/13".

**One more off-by-one, in `#obligations`.** "Every one of the **fourteen**
non-defining rows is a claim about the grade itself" — the classification
table has 17 rows, two of them defining (`join_comm`, `join_idem`), so
fifteen. The later "worth keeping distinct from the other fourteen"
should then be thirteen — and `tmp/plan/checklist.md`'s step-21 line
carries the same "all 14 non-defining … consumers", so the two documents
agree with each other and not with the table they describe. The table
itself is *correct and still complete*:
`--by-property` currently tags exactly 7 theorems `commutative` and 10
`idempotent`, and every one of them appears in the table. Only the two
sentences counting it are wrong.

**Minor.** The `traverse` row's "(9 laws + bridge)" is 10 non-bridge
theorems; the `flatten` row's "(9 laws + bridge)" is exact. Nothing
depends on either.

**The "proof lines" columns in the three measurement tables are not one
measurement.** Not part of the summary table, but the same family of
defect and it undercuts the tables the summary was assembled from.
`#monad`'s table (`:340`) counts **proof body lines** — `bind_assoc` 21,
`bindK_assoc` 13, both exact. `#applicative`'s continuation table
(`:358`) and `#traverse`'s table (`:788`) count **whole declarations,
signature included** — `ap_comp` 23, `apK_comp` 16, `traverseK_cons` 3,
all exact under *that* rule and none under the first. Same column header
in all three. Two rows match neither: `traverseK_nil_eq_fromEmpty` and
`traverseK_irrel` are listed at 1 line and are 2
(`Graded/Sufficient.lean:349-350`, `:362-363`). And the parenthetical at
`:353` credits the numbers to "`scripts/laws-inventory.py`'s own
chunker" — the script's `theorem_chunks` exists but only feeds the
property mention-scan; it computes no line counts and prints none. These
columns are hand-counted, under two rules, and support no conclusion on
their own. Either normalize them to declaration lines or drop them; the
cast columns are the ones carrying the argument.

**One row in `#applicative`'s table denies a baseline it names.**
`ap_flip → apK_flip` is given as "— (new law, no union-graded
proof-line baseline to compare against)". `Graded.ap_flip`
(`Applicative.lean:163-172`) is the baseline, is structurally identical
(`rcases`, then the same four constructor cases), and is **10** lines
against `apK_flip`'s **10** (`Sufficient.lean:283-292`). The honest entry
is 10 → 10: the sufficient-grade proof is not shorter, it is the same
shape with the `cast_ok`/`cast_err` rewrite dropped from every branch.
Which is a *better* datum for the argument than a dash, because it
separates "fewer lines" from "no property cited".

---

## 5. `grade-join-strength`: still OPEN is defensible, but the question has drifted off its own title

**Keeping it open is right in the narrow sense** that nobody has ruled and
no code decides it. Both narrowings are honest: [obligation-layering]
showed no operational law needs either axiom, and [sufficient-grade-nested]
checked whether the traversal leg had incidentally produced the
non-lattice-`Pomonoid`-with-working-`traverse` case that would force the
stronger reading, and correctly reported that it had not.

**But two narrowings that both conclude "the migration did not produce
case (b)" is a pattern, not a coincidence.** Every leg of this migration
is concrete, on `Grade Err`; the abstract framework where `Nat` lives was
never touched and, on the plan as it stands, never will be. A third
narrowing will report the same thing. That is the sign of a question
whose *stated* form is no longer the live one.

The title asks whether a grade's `join` must be a least upper bound. The
migration has answered the only part of that a proof can answer: **no
operation needs it, and a nominated bound needs nothing algebraic at
all.** What is left is not an algebra question. It is a wording question
about `traverse`: *is the traversal's result error set nominated (deduced
from the element function, per §1.3) or folded?* Only the folded reading
puts idempotence in the requirements, and this run has shown the folded
reading was a modelling choice, not a necessity.

**The cheapest thing that settles it is a ruling, not a build.** The
anchor's own option (a) — "an explicit P3200 design decision that
`traverse` is offered only for `error_set`-like grades" — costs one
paragraph, and the evidence for taking it is now complete: nothing
operational is lost, because nothing operational ever needed the promise.
Option (b) is not cheap and should not be priced as if it were: producing
a genuine non-lattice grade with a working `traverse` requires an abstract
carrier `Graded (G) (g : G) α` over `[Pomonoid G]`, which does not exist —
`Graded/Obligations.lean` has grades without carriers and
`Graded/Carrier.lean` has one carrier over one grade. That is a leg of
work, not a spike, and it would be building an instance nobody wants in
order to settle a question a sentence closes.

**Recommendation.** Graduate it in place rather than leaving it to accrete
a third negative check: revise the **Question** line to the live form
("nominated or folded?"), keep the slug and every link, and either record
the ruling or record explicitly that the question is parked pending a
P3200 decision and will not be advanced by further legs of this
migration. As it stands, a reader arrives at a question whose own text
says the code cannot answer it, under a status that implies more code
might.

---

## 6. `docs/design.md`: what a reader would trip over

Nine items. The first three are the ones that matter.

1. **`## laws-inventory` opens with a count that is 57 short.** "The
   table: `docs/laws.md` (146 theorems…)" — it is 203. This is the
   section a reader reaches *from* `docs/laws.md`, and the whole section
   describes the union-graded model with no note that a second layer now
   sits in the same table.

2. **`## laws-inventory` still describes the superseded class hierarchy.**
   "What a different grade pomonoid must supply" names "`Pomonoid`,
   `IsCommPomonoid extends Pomonoid`, `IsIdemPomonoid extends
   IsCommPomonoid`" and "that hierarchy's three layers".
   [obligation-layering] deleted that nesting three steps ago:
   `Graded/Obligations.lean` now has four classes, `IsIdemPomonoid
   extends Pomonoid` directly, and `IsCanonicalPomonoid` on top. A
   superseded account left standing, of exactly the kind `#obligations`'s
   own revision note was careful to flag at its own head.

3. **`## provisional-decisions` calls a CLOSED question OPEN.** The
   `[#monad](#cast-burden-migration-scope)` entry reads "**OPEN
   question** `cast-burden-migration-scope`… Deliberately unplanned until
   the first two steps' measurements exist." That question was closed by
   this migration and its own anchor says **CLOSED**. The index's own
   convention for this is already established one entry down
   (`graded-traversable-composition`, kept and marked CLOSED); apply it.

4. **The same entry's neighbour repeats the superseded hierarchy.**
   `[#obligations](#grade-join-strength)` ends "the three-layer account
   applies only to the weaker one".

5. **The index no longer describes itself.** It opens "Index of every `>
   **Provisional.**` mark in this document, by anchor", and lists eight
   entries; the document contains five such marks (lines 23, 98, 152,
   594, 1501). Two entries (`#monad`, `#obligations`) index no mark at
   all — they index open questions. That drift predates this migration,
   but item 3 makes it visible: an entry that indexes nothing and is also
   wrong about status. Either retitle the section ("provisional marks and
   open questions") or split it.

6. **`#morphisms`'s provisional mark now sits under a revised account.**
   The paragraph above line 1501 tells the reader to read `GradedHom` as
   one sufficient instance of a weaker obligation; the mark below it then
   discusses what "`GradedHom` asks of `gmap`/`hom`" as though it were
   the definition. The mark's content (no injectivity, no surjectivity)
   is still true; its framing is one revision behind. Cheap fix: one
   clause pointing forward.

7. **`blog/letters/sufficient-grade-bind.org:15` carries the corrected
   count's predecessor**: "39 of 146 theorems (26%) carry a `cast`". The
   figure is 38. The percentage is unaffected (26.0% vs 26.7%), which is
   presumably why it survived the `581da13` sweep. This is the published
   letter, so it is the one occurrence that matters. Two of the remaining
   three are the deliberately-frozen worker briefs
   (`step-sufficient-grade-bind.md:16`,
   `step-sufficient-grade-applicative.md:31`) and should stay as they
   are; the third, `tmp/plan/README.md:130`, is a living plan document
   and was not covered by that reasoning.

8. **"six casts" in three places in `design.md` and one letter** — §4.

9. **"Leg" means two different things in two adjacent documents.**
   `#cast-burden-migration-scope` says the design "held across all five
   legs" (`docs/design.md:2376`, `:2384`, `:2388`) and counts one leg per
   step; `#compose`'s subsection says "the last of three legs"
   (`:1285`), and `handoff-migration-review.md` calls the whole run
   three-leg. Both readings are defensible — five structures, three
   conceptual groupings — but a reader moving between the anchor and the
   handoff will read one of them as a miscount. Pick one word.

None of these is a soundness problem. Items 1, 2 and 3 are the ones that
would actively mislead: a stale total, a superseded hierarchy, and a
status marker pointing the wrong way.

---

## 7. Metrics, steps 19–24

Six rows, six separate `model: sonnet` contexts, one per step. Four of the
six state in their own `note` that they ran the edit-verify loop in their
own context and dispatched no sub-agents (`applicative`,
`obligation-layering`, `morphism`, `nested`); `bind` and `traverse` record
it neither way and rest on the orchestrator's confirmation. Promoted to
`metrics/fanout-runs.jsonl` as `run: lean-model-2`,
`branch: integration/lean-model`.

| step | wall | verify runs | edit iterations | proof attempts | files | +ins | −del |
|---|---|---|---|---|---|---|---|
| 19 `sufficient-grade-bind` | 1067 s | 6 | 7 | 1 | 12 | 584 | 12 |
| 20 `sufficient-grade-applicative` | 1681 s | 3 | 3 | 0 | 10 | 802 | 3 |
| 21 `obligation-layering` | 1368 s | 8 | 24 | 2 | 12 | 771 | 316 |
| 22 `sufficient-grade-traverse` | 848 s | 12 | 13 | 1 | 11 | 631 | 3 |
| 23 `sufficient-grade-morphism` | 1106 s | 7 | 6 | 9 | 9 | 590 | 7 |
| 24 `sufficient-grade-nested` | 1991 s | 11 | 19 | 2 | 11 | 1251 | 45 |
| **total** | **8061 s (2 h 14 m)** | 47 | 72 | 15 | — | 4629 | 386 |

**What a leg costs now that the technique is routine.** Mean 1344 s
(22 min), median 1237 s; the five sufficient-grade legs alone mean 1339 s,
median 1106 s. Roughly 770 inserted lines, 8 verify runs, 12 edit
iterations and 2–3 proof attempts per leg.

**The comparison that matters is not "faster".** Against the 17 non-degenerate
steps of `lean-model-1` (mean 1045 s, median 937 s, 611 insertions), a
migration leg is about 30% *longer* in wall time and about 25% larger in
output. Insertions per minute are indistinguishable: **35.1** in run 1
against **34.5** in run 2. The technique becoming routine did not make a
step cheaper; it made a step *bigger* at the same throughput. Every leg
came back GREEN first time, none was blocked, and the run's only two
schema/data defects were bookkeeping (`8626f70`, `581da13`), not proofs.

**The edit/verify split is where the second run differs, and it is a
better instrument.** Run 1 recorded a single `attempts`; run 2 splits it
into `verify_runs` / `edit_iterations` / `proof_attempts`, and the split
immediately pays: `sufficient-grade-morphism` has the run's *lowest* edit
count (6) and its *highest* proof-attempt count (9), which a single
`attempts` number would have flattened into "about average". That is the
leg whose brief came from a spike with an open proof leaf. Conversely
`obligation-layering` has 24 edit iterations and 2 proof attempts — a
restructuring leg, not a proving one. Keep the three-way split; the rows
are marked `attempts_comparable: false` against run 1 because run 1 has
no comparable field.

**Two data defects in the source rows, corrected on promotion.** Three of
the six rows (20, 23, 24 by file order) self-tagged `"run":
"lean-model-1"`, which is wrong — they are the second run on the same
branch. `obligation-layering`'s row carries its diff fields flat
(`files_changed`/`insertions`/`deletions` at top level) instead of under
`diff`, and has no `lane`. The promoted rows set `run: lean-model-2`,
add the `diff` object and `lane: null`, and are otherwise verbatim.

**Standing recommendation, restated because this run hit it twice.**
Every metrics row in this repo is assembled by `printf` inside a shell
command. That has now produced an invalid `\'` JSON escape
(`8626f70`) and a `wall_seconds: 1788879160` from an empty `$START`
(rows 16/17). Both are the same defect: JSON built by string
concatenation in a shell. A three-line `python3 -c 'import json,sys;
print(json.dumps(...))'` in `AGENT-PROMPT.md` removes the whole class,
and would also stop workers inventing per-row schema drift.

---

## 8. Recommendations, ordered

**Fix before the next reader**

1. `#cast-burden-migration-scope`'s `Traverse` row: `2/12` → `1/12` (§4).
   The column then sums to the corrected 38.
2. `Comp.ap_interchange`: "six casts" → "four" at `docs/design.md:363`,
   `:370`, `:560`, `:2434`,
   `blog/letters/sufficient-grade-applicative.org:25` and
   `tmp/plan/checklist.md`'s step-20 line (§4). The claim it supports
   survives.
3. `## laws-inventory`: "146 theorems" → 203, and one sentence saying the
   table now holds two layers (§6.1).
4. `## laws-inventory`'s "What a different grade pomonoid must supply":
   replace the three-nested-class description with `Obligations.lean`'s
   current four-class shape (§6.2).
5. `## provisional-decisions`: mark `cast-burden-migration-scope` CLOSED
   (§6.3); drop "three-layer" from the `grade-join-strength` entry
   (§6.4).
6. `blog/letters/sufficient-grade-bind.org:15`: 39 → 38, and
   `tmp/plan/README.md:130` likewise. Leave the two frozen step briefs
   alone (§6.7).
7. `#obligations`: "fourteen non-defining rows" → fifteen, "the other
   fourteen" → thirteen, and the same figure in `tmp/plan/checklist.md`'s
   step-21 line (§4).

7a. The three "proof lines" columns: normalize to one rule (declaration
   lines is the one two of the three already use), fix the two rows that
   match neither, drop the false attribution to `laws-inventory.py`, and
   give `ap_flip → apK_flip` its real 10 → 10 (§4).

**Judgment calls for the orchestrator**

8. Replace the "structures bridge differently from operations" framing
   with the field-list account in §3, and record `GradedHomK`'s
   payload-naturality obligation by name. Keep `GradedHom.gmap_mono`
   untagged.
9. `grade-join-strength`: revise the Question line in place to the
   nominated-or-folded form and either rule on option (a) or record that
   it is parked pending a P3200 decision (§5).
10. Decide whether `Accum` gets a fourth leg. The table's own row is the
    right brief for it, and it is the only structure in the model with
    no sufficient-grade layer and no recorded reason it could not have
    one — only a reason it would be a different-shaped question.

**Process**

11. Emit metrics rows with `json.dumps`, not `printf` (§7).
12. Say in `AGENT-PROMPT.md` which `run` label the current fan-out uses;
    three of six workers guessed and guessed wrong (§7).
