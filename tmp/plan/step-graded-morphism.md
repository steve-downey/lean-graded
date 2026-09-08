# step: graded-morphism

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

## Why

Traversable's naturality law quantifies over *applicative morphisms*.
In the graded setting a morphism between graded structures has to say
what it does to grades. The C++ has exactly one such thing in practice:
renaming or coarsening error types (`error_set<A,B>` → `error_set<C>` by
mapping both to `C`). That is a monoid homomorphism on grades
(`Finset.image`) together with a natural family on carriers. This step
defines it, proves it is a graded monad morphism, and proves the
naturality law of `traverse` against it. The finding to record: which
pomonoid properties `Finset.image` preserves for free (union, ∅ —
i.e. it is a homomorphism of *join-semilattices*) so the paper can say
what a "grade morphism" must be.

## What already exists

`docs/design.md#traverse` (`traverse`), `#monad`, `#subsumption`,
`#carrier`, `#grade`.

## The change

Create `Graded/Morphism.lean`:

```lean
variable {Err' : Type u} [DecidableEq Err']

def Grade.rename (φ : Err → Err') : Grade Err → Grade Err' := Finset.image φ

def rename (φ : Err → Err') : Graded g α → Graded (Grade.rename φ g) α
  | .ok a     => .ok a
  | .err e he => .err (φ e) (Finset.mem_image_of_mem φ he)
```

- `rename_join : Grade.rename φ (join g h) = join (rename φ g) (rename φ h)`
  and `rename_bot` — the homomorphism (uses `Finset.image_union`,
  `image_empty`; tag `/-- PROPERTY: homomorphism -/`).
- `rename_mono : g ⊆ h → rename φ g ⊆ rename φ h` (order preserved).
- `rename_map`, `rename_pure`, `rename_bind : rename φ (bind x f) =
  cast (rename_join ..) (bind (rename φ x) (rename φ ∘ f))`,
  `rename_widen`.
- `structure GradedHom` packaging `(φ, rename, rename_join, rename_bot,
  rename_bind, rename_pure)` — the definition of "graded monad
  morphism" the C++ design lacks. Provisional: whether the grade map
  must be surjective/injective for anything; expect "no".
- Naturality of traverse: `rename φ (traverse f xs) = traverse (rename
  φ ∘ f) xs` (up to `cast`/`widen_irrel`). The proof is by induction on
  `xs` using `traverse_cons` and `rename_bind`.
- `rename_toGraded`: `Accum` from [applicative-accumulation] also
  admits `rename`; show `toGraded` commutes with it. If this turns into
  more than a few lines, drop it and note that in the living doc rather
  than spend a block on it.

### Consumer

`Examples/Validation.lean`: coarsen `{parse, range}` to a single
`inductive E' | bad` via `fun _ => E'.bad`; `#check` the resulting grade
is `{E'.bad}`; `#guard` the value.

### Tests

`Tests/Morphism.lean`.

### Living doc

`docs/design.md#morphisms`: the definition of graded morphism, what
`Finset.image` preserves, the naturality law status.

### Letter

`blog/letters/graded-morphism.org`, title "Renaming your errors is a
homomorphism". "Back in C++": the `transform_error`-style operation on
a graded expected has laws, and here they are.

## Declared file scope

`Graded.lean`, `Graded/Morphism.lean`, `Tests.lean`, `Tests/Morphism.lean`,
`Examples/Validation.lean`, `docs/design.md` (`#morphisms`),
`blog/letters/graded-morphism.org`.

## Spot checks

```
grep -n "PROPERTY: homomorphism" Graded/Morphism.lean
grep -n "theorem traverse_rename\|naturality" Graded/Morphism.lean
```

## Setup

```
cd __MAIN_CHECKOUT__
git worktree add ../wt-graded-morphism -b step/graded-morphism integration/lean-model
cd ../wt-graded-morphism
ln -s __MAIN_CHECKOUT__/.lake .lake 2>/dev/null || true   # reuse the Mathlib cache; if Lake objects, run 'lake exe cache get' here instead
START=$(date +%s)
```

## Verify GREEN baseline

```
make verify > /dev/null; echo verify=$?      # must be 0
make nosorry; echo nosorry=$?                # must be 0
```
If either is non-zero before you change anything, stop: `blocked-graded-morphism.md`
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
git add -A
git commit -F- << 'MSG'
graded-morphism: grade-respecting morphisms (error renaming); naturality of traverse

Defines what a graded monad morphism is for this design, shows error
renaming is one because Finset.image is a join-semilattice
homomorphism, and proves the naturality law of traverse against it.
This is the law set behind transform_error on a graded expected.
MSG
cd __MAIN_CHECKOUT__
git checkout integration/lean-model
git merge --no-ff step/graded-morphism -m "merge step/graded-morphism [graded-morphism]"
```

## Record measurements

Before cleanup, from the worktree (so `build.log` and the diff still exist):

```
END=$(date +%s)
cd ../wt-graded-morphism
printf '%s\n' '{"step":"graded-morphism","lane":null,"outcome":"green","wall_seconds":'"$((END-START))"',"attempts":<n>,"verify":{"command":"make verify","exit_code":0,"wall_seconds":'"$((V1-V0))"',"log_bytes":'"$(wc -c < build.log)"',"summary_lines_read":20},"diff":'"$(git diff --shortstat integration/lean-model~1...step/graded-morphism | awk '{printf "{\"files_changed\":%d,\"insertions\":%d,\"deletions\":%d}",$1,$4,$6}')"',"out_of_scope":[],"note":""}' >> __MAIN_CHECKOUT__/tmp/plan/metrics.jsonl
```
Fill `attempts` honestly (a blocked attempt is also a row, with
`"outcome":"blocked"`, appended before cleanup). List any out-of-scope file.

## Cleanup

```
cd __MAIN_CHECKOUT__
git worktree remove --force ../wt-graded-morphism
git branch -d step/graded-morphism
```

## Handoff

Mark `graded-morphism` done in `tmp/plan/checklist.md`. Read
`tmp/plan/step-canonical-representation.md`. Write `tmp/plan/handoff-canonical-representation.md` fresh, per
the contract in `AGENT-PROMPT.md`.
