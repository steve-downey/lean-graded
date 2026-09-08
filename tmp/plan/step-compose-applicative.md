# step: compose-applicative

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

Added after the original plan, to answer the open question
[graded-traversable-composition](../../docs/design.md#graded-traversable-composition)
that [compose-flatten] opened and could not close.

## Why

[compose-flatten] refuted a composition law, but not the one the
classical theory states. It tested the **flattened** form — nested
carriers collapsed to the union grade — and found it false, with a
counterexample that survives at a single grade and therefore says
nothing about grading at all. The classical Traversable composition law
is about `Compose F G` with the two functors kept **separate**; for
graded functors the natural grade of `Graded g (Graded h α)` is the
**pair** `(g, h)` in the product pomonoid, joined componentwise. That
structure has never been built here, so the law in its proper form is
untested, not refuted.

This step builds it and states the law against it. The finding either
way is worth having: if the law holds, P3200 can say composition is fine
provided you do not flatten first, and the earlier counterexample
becomes a precise warning rather than a defect. If it fails even for the
product-graded composite, that is a real result about graded
traversables and the first one this model has produced.

The second deliverable is the *explanation*: whether `flatten` is an
applicative morphism from the product-graded composite to the
union-graded carrier. That question is what the earlier refutation was
really about — flattening forgets which layer failed — and answering it
turns "the flattened law is false" from an anecdote into a statement
about what the forgetful map does and does not preserve.

## What already exists

`docs/design.md#compose` (`flatten`, `swap`, the eight flattening laws,
and the open question), `#traverse` (`traverse`, `foldGrade`,
`foldGrade_le`, `foldGrade_cons_ne_nil`), `#applicative` (`ap`, `map2`,
the four laws), `#grade`, `#carrier`.

## The change

Create `Graded/ComposeApp.lean`.

The composite carrier, with the product grade kept as two separate
indices — **not** joined:

```lean
def Comp (g h : Grade Err) (α : Type u) : Type u := Graded g (Graded h α)

def Comp.pure (a : α) : Comp (Grade.bot : Grade Err) Grade.bot α :=
  Graded.ok (Graded.ok a)

def Comp.map (f : α → β) : Comp g h α → Comp g h β := map (map f)

/-- The composed applicative: outer layers combine with the outer `ap`,
    inner layers with the inner `ap` lifted inside — exactly `Compose`'s
    own instance. The grade is the *pair* `(g ⊔ g', h ⊔ h')`, joined
    componentwise: the product pomonoid. -/
def Comp.ap (ff : Comp g h (α → β)) (xx : Comp g' h' α) :
    Comp (Grade.join g g') (Grade.join h h') β :=
  map2 (fun f x => ap f x) ff xx
```

Theorems, each citing the property it consumes, in both components:

- `Comp.map_id`, `Comp.map_comp` — functor laws, expect no named property.
- The four applicative laws for `Comp.ap`, named `Comp.ap_pure_id`,
  `Comp.ap_pure_pure`, `Comp.ap_interchange`, `Comp.ap_comp`. Expect
  each to need, in **each component independently**, exactly what the
  single-layer law needed in [applicative-from-monad]: unit and
  associativity, never commutativity. Use that step's two-cast technique
  for interchange (`docs/design.md#applicative`) so it stays comm-free;
  here it applies twice, once per component. **The finding to record: no
  law should need any relationship between `g` and `h`.** They are
  independent coordinates of a product; if a proof wants them related,
  stop and say so, because that would mean the product pomonoid is not
  the right structure after all.
- `Comp.foldGrade_le'`-style plumbing as needed so that a uniform
  composite traversal has grade `(g, h)`: reuse `Graded.foldGrade` and
  `foldGrade_le` from [traverse-list] once per component. Do **not**
  write a second `foldGrade`.
- `traverseComp (f : α → Comp g h β) (xs : List α) : Comp g h (List β)`
  — the traversal in the composed applicative, uniform-grade in both
  components, built the same way `traverse` was: `widen` along
  `foldGrade_le` in each component rather than `cast` along the
  idempotence equality, so the empty list needs no special case.

### The law this step exists for

```lean
theorem traverseComp_eq (f : α → Graded g β) (k : β → Graded h γ) (xs : List α) :
    traverseComp (fun a => map k (f a)) xs = map (traverse k) (traverse f xs)
```

Note what is *absent*: no `flatten`, and both sides live in
`Graded g (Graded h (List γ))` with the two grades still separate. This
is the classical law's actual shape. State it with whatever `cast` the
uniform-grade collapse forces (expect one per component, along
`join_idem`, mirroring `traverse_cons`), and no more.

If it holds, say which properties it consumed. If it fails, produce a
counterexample confirmed by `#eval` — not a hand argument — exactly as
[compose-flatten] did, and record it. **A refutation here is a genuine
result about graded traversables and is a successful outcome for this
step, not a block.** Only an inability to state or test it is a block.

### The explanation deliverable

```lean
theorem flatten_ap : flatten (Comp.ap ff xx) = cast _ (ap (flatten ff) (flatten xx))
```

i.e. is `flatten` an applicative morphism from the product-graded
composite to the union-graded carrier? Expect a grade cast reassociating
`(g ⊔ g') ⊔ (h ⊔ h')` into `(g ⊔ h) ⊔ (g' ⊔ h')`, which needs
associativity **and commutativity** — the second appearance of
`join_comm` in the model, and worth flagging as such. If the equation
holds only under a condition, state the condition; if it fails outright,
that failure *is* the explanation for [compose-flatten]'s counterexample
and should be cited from that open question's Log. Either way this is
the theorem that says precisely what flattening destroys.

### Consumer

`Examples/Validation.lean`: the same two-stage `parseNat`/`checkRange`
pipeline run through `traverseComp` without flattening, `#guard`ed, and
the [compose-flatten] counterexample shape (`f` failing late, `k`
failing early) run through *both* the composed traversal and the
flattened one, showing on one screen that they differ and which is which.

### Tests

`Tests/ComposeApp.lean`: each law at `E`; a `#guard` that computes.

### Living doc

`docs/design.md#compose`: the `Comp` subsection — the product pomonoid,
the composed `ap`, the law's status, and the `flatten`-morphism result.
Then **update the open question
[graded-traversable-composition](../../docs/design.md#graded-traversable-composition)
in place**: move what this step settles out of "not tested" and into
"settled", append a dated Log entry, and change `Status:` if the question
is now closed. Do not open a second question for the same subject.

### Letter

`blog/letters/compose-applicative.org`, title "The composition law was
about a structure we hadn't built". "Back in C++": nesting `expected`
and collapsing to the union grade is safe for everything in
`#compose`'s eight laws, but the collapse is a lossy map, and the
composition law is a claim about the *unflattened* thing. Say plainly
that the earlier letter's counterexample refuted a statement nobody
should have made, and that this letter tests the one they should.

## Declared file scope

`Graded.lean`, `Graded/ComposeApp.lean`, `Tests.lean`,
`Tests/ComposeApp.lean`, `Examples/Validation.lean`, `docs/design.md`
(`#compose` and the `graded-traversable-composition` question),
`blog/letters/compose-applicative.org`.

## Spot checks

```
grep -n "flatten" Graded/ComposeApp.lean     # only in flatten_ap and its docs
grep -c "def foldGrade" Graded/ComposeApp.lean   # 0 — reuse Traverse's
grep -n "Status:" docs/design.md              # the open question's status updated
```

## Setup

```
cd /home/sdowney/src/lean-graded
git worktree add ../wt-compose-applicative -b step/compose-applicative integration/lean-model
cd ../wt-compose-applicative
ln -s /home/sdowney/src/lean-graded/.lake .lake 2>/dev/null || true   # reuse the Mathlib cache; if Lake objects, run 'lake exe cache get' here instead
START=$(date +%s)
```

Note: `Graded/Compose.lean` pins its payload types to `Type u` (the same
universe as `Err`) because `Graded h α` lives in `Type (max u v)` while
`bind` ties its payloads to one universe. `Comp` nests two carriers and
will meet the same constraint; pin payloads to `Type u` in this file too
and say so in the living doc rather than fighting it.

## Verify GREEN baseline

```
make verify > /dev/null; echo verify=$?      # must be 0
make nosorry; echo nosorry=$?                # must be 0
```
If either is non-zero before you change anything, stop: `blocked-compose-applicative.md`
(the integration branch is broken; not your step to fix).

## Verify GREEN after

```
V0=$(date +%s); make verify > /dev/null; echo verify=$?; V1=$(date +%s)
make nosorry; echo nosorry=$?
make letters; echo letters=$?
```
All zero. Read `tail -n 20 build.log` only; never the whole log.

## Commit and merge back

```
git add <your files by name>
git commit -F- << 'MSG'
compose-applicative: the composed applicative with the product grade, and the law stated against it

compose-flatten refuted a flattened composition law that the classical
theory never stated. This builds the structure the law is actually
about — two grades kept separate as a product pomonoid, outer layers
combined with the outer ap and inner with the inner — and states the
law against that. flatten's status as an applicative morphism is what
explains the earlier counterexample.
MSG
cd /home/sdowney/src/lean-graded
git checkout integration/lean-model
git merge --no-ff step/compose-applicative -m "merge step/compose-applicative [compose-applicative]"
```

Stage your files **by name**; do not use `git add -A` in the main
checkout. See the note in your inbound handoff.

## Record measurements

Before cleanup, from the worktree (so `build.log` and the diff still exist):

```
END=$(date +%s)
cd ../wt-compose-applicative
printf '%s\n' '{"step":"compose-applicative","lane":null,"outcome":"green","wall_seconds":'"$((END-START))"',"attempts":<n>,"verify":{"command":"make verify","exit_code":0,"wall_seconds":'"$((V1-V0))"',"log_bytes":'"$(wc -c < build.log)"',"summary_lines_read":20},"diff":'"$(git diff --shortstat integration/lean-model~1...step/compose-applicative | awk '{printf "{\"files_changed\":%d,\"insertions\":%d,\"deletions\":%d}",$1,$4,$6}')"',"out_of_scope":[],"note":""}' >> /home/sdowney/src/lean-graded/tmp/plan/metrics.jsonl
```
Fill `attempts` honestly (a blocked attempt is also a row, with
`"outcome":"blocked"`, appended before cleanup). List any out-of-scope file.

## Cleanup

```
cd /home/sdowney/src/lean-graded
git worktree remove --force ../wt-compose-applicative
git branch -d step/compose-applicative
```

## Handoff

Mark `compose-applicative` done in `tmp/plan/checklist.md`. Read
`tmp/plan/step-oracle-export.md`. Write `tmp/plan/handoff-oracle-export.md` fresh, per
the contract in `AGENT-PROMPT.md`.
