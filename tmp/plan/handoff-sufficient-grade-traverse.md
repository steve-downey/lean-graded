# handoff → sufficient-grade-traverse

Written by the orchestrator. You are the first of three legs in a
migration planned after [obligation-layering], so there is no predecessor
step to have written this.

Goal and merge criterion: fixed by `step-sufficient-grade-traverse.md`.

## The tree you branch from

Twenty-one steps done and merged on `integration/lean-model`. `make all`
(`verify nosorry letters laws`) exits 0 with **zero build warnings**, tree
clean, 174 theorems in the generated table.

`Graded/Sufficient.lean` is the cast-free layer built by three earlier
steps: `bindK`, `pureK`, `apK`, `map2K`, `apFlippedK`, `traverseK`, their
reduction lemmas, `bindK_irrel`, and three `/-- BRIDGE -/` theorems tying
each operation back to its union-graded original. **No statement in that
file carries a cast**, verified. You extend it.

## What `traverseK` already establishes, and what it does not

`traverseK`, `traverseK_nil`, `traverseK_cons` are on disk, all `rfl`. It
folds no grade: every element lands at a caller-supplied `k` directly.
`traverseK_cons` is cast-free where `Graded.traverse_cons` carries a
`cast (Grade.join_idem g)`.

**Narrowly, that is all it establishes.** It was added as a bounded probe
by a step whose subject was the obligation layering, not this migration,
and that step was explicit: no `traverse_map`, `traverse_length`,
identity-law or `traverse_rename` analogues, no interaction with
`Comp.traverseComp_cons`. Building those is your leg. One theorem proving
`rfl` is not the claim that a whole leg is free, and your step file asks
you to confirm it rather than inherit it.

**A caveat on the evidence, because it was overstated once.** The
orchestrator's original spike contained a `traverseK_grade` "theorem" that
read `traverseK hg f xs = traverseK hg f xs := rfl` — a tautology proving
nothing about grades. It is not on disk and must not be reintroduced or
cited. The honest statement of what changes is narrower: length-independence
stops being a *theorem* and becomes a property of `traverseK`'s
*signature*, since the result type is `Graded k (List β)` for every list
before any theorem is stated.

## The claim your leg is really testing

Five of the model's nine idempotence citations live in
`Graded/Traverse.lean`: `foldGrade_cons_ne_nil`, `traverse_cons`,
`traverse_cons_err_left`, `traverse_cons_ok_err`, `traverse_fromEmpty`.
[obligation-layering] classified every one as a canonicalization fact,
having checked each proof's case split individually rather than filing them
as a family: idempotence appears only in a cast target, never in the step
that picks the resulting value.

So the prediction is not "the casts get cheaper" but "**`foldGrade` and
`foldGrade_cons_ne_nil` have no analogue at all**". If you find yourself
writing a `foldGradeK`, stop and ask what it is for. A genuine need for one
refutes that classification, and is worth more than a confirmation.

## `make laws` goes red until you regenerate, and the allow-list is not a dumping ground

`docs/laws.md`/`docs/laws.json` are generated from `Graded/*.lean` by
`scripts/laws-inventory.py`; `make laws` regenerates and then
`git diff --exit-code`s them, so adding theorems fails the check until you
run `python3 scripts/laws-inventory.py` and commit the result.

The script's property attribution is a deliberately dumb
mentions-in-proof-text heuristic and exits 1 naming any theorem citing no
tagged property and not on its `ALLOWLIST` (46 entries, each with a
one-line reason). Your reduction lemmas and the bridge will trip it. Add
them with an individually justified reason each; never widen the list to
get green. Three chunking bugs have been found in that script so far
(backward bleed, forward bleed, and a `--` comment before a `/-- ... -/`
theorem crediting the previous theorem) — if a row surprises you, suspect
the parser and read the source before you suspect the proof. It also has a
`--by-property` reporting mode, added by [obligation-layering].

## Metrics schema

`verify_runs` / `edit_iterations` / `proof_attempts`. Do not emit
`attempts`: the integration review found it conflated three quantities and
never measured the stop rule it was named for. `proof_attempts` is the
number the three-strikes rule is about.

The shell does not persist between tool calls, so a `START` set earlier is
empty. Write timestamps to a file in `/tmp`, **not** inside the worktree —
one worker committed one there and needed a second commit to remove it, and
another shipped `wall_seconds: 1788879160` from exactly this.

## Live elaboration gotchas

- **Reduction lemmas before laws.** Every leg that reached for
  `change`/manual unfolding first paid for it. The specific trap:
  `cases h : f a` does not reach an occurrence of `f a` under a lambda
  whose binder shadows `a` — reduce with your `traverseK_cons`-style lemma
  first, then case. This is where two spikes stalled.
- Inside a dotted declaration a bare reference to a same-named function
  resolves to the declaration being defined; `def Comp.apK ... := apK ...`
  silently recursed and cost a previous leg real time. Qualify fully if you
  nest names.
- `abbrev`, not `def`, for anything instance search must see through.
- `Graded g α` lives in `Type (max u v)`, not `Type v`, because `err` holds
  an `Err : Type u`. Ascribe universes on wrapper abbreviations.
- A bare `pure` in `Tests/*.lean` or `Examples/*.lean` is ambiguous with
  Mathlib's `Pure.pure`; write `Graded.pure`/`Graded.pureK`. A `#guard`
  cannot carry a `/-- ... -/` doc comment. `#guard` on two `Graded g α`
  values directly has never worked — route through a render-to-`String`
  function; every consumer has its own.

## A green build is a silent build

Zero warnings currently, so any warning is yours. Three inherited Mathlib
lint rules are off in `lakefile.toml` because they contradict this project
(one forbids the `#guard` that `docs/RULES.md` requires). Do not touch that
file; it is an "ask".

## Register, and staging

Letters carry the author's own editorial register: addressee `"Steve,"`,
signature `"--SMD"`, **no em-dashes** — colons, parentheses or full stops.
Yours is Letter 20. Do not run a voice tool over any existing letter.

The main checkout's tree is clean and should stay that way: stage your own
files by name there. `git add -A` is fine inside your worktree only.

## What your leg hands on

`step-sufficient-grade-morphism.md` follows, and it works on a *structure's
field types* rather than theorem statements. Tell it which of your
reduction lemmas generalise beyond `List` and which were list-specific,
because it has no list in it at all.
