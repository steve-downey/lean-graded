# handoff → obligation-layering

Written by the orchestrator. [sufficient-grade-applicative] handed off to
the migration question, not to this step, because this step was planned
after it finished.

Goal and merge criterion: fixed by `step-obligation-layering.md`.

## The finding that prompted your step, in the form you can check

From `docs/laws.json`, generated, not asserted:

```
ap_flip              ['commutative']        apK_flip             []
ap_interchange       ['unit']               apK_interchange      ['order']
Comp.ap_interchange  ['unit']               Comp.apK_interchange ['order']
ap_comp              ['associative','unit'] apK_comp             ['order']
```

`apK_flip` consumes nothing at all. The same pattern held one layer down:
`bind_pure_left`/`_right` went from `['order','unit']` to `['order']`, and
`bind_assoc` from `['associative','order']` to `['order']`. Across seven
laws in two layers: order lemmas in, unit and associativity out, and
commutativity gone entirely.

## What is on disk that you need

`Graded/Sufficient.lean` holds the cast-free layer: `bindK`, `pureK`,
`apK`, `map2K`, `apFlippedK`, their reduction lemmas, the cast-free laws,
`bindK_irrel`, and two `/-- BRIDGE -/` theorems (`bind_eq_bindK`,
`ap_eq_apK`) tying each back to its union-graded original. **No statement
in that file carries a cast** — verified. Extend it with the `traverseK`
probe your step file specifies and nothing else.

`Graded/Obligations.lean` holds `Pomonoid`, `IsCommPomonoid`,
`IsIdemPomonoid`, the `Finset` instances built by citing
`Graded/Grade.lean`'s named lemmas, the `Nat` counter-instance
(commutative, not idempotent), `foldG`, `joinAllG`, and the executable
disproofs at `Nat`. Note that `join_le` there is a *theorem* recovered
from `join_mono` + `join_idem`, not a class field, and that this is why
`foldG_le` needs `IsIdemPomonoid` where the concrete `foldGrade_le` needs
only order. That asymmetry is a good example of the distinction your
classification is drawing, and worth a row in your table.

## `scripts/laws-inventory.py`, and its three parser bugs so far

Its property attribution is a deliberately dumb mentions-in-proof-text
heuristic that exits 1 naming any theorem citing no tagged property and
not on its `ALLOWLIST` (currently 45 entries, each with a one-line
reason). Three chunking bugs have been found and fixed in it: backward
bleed absorbing a preceding theorem's text, forward bleed absorbing a
following docstring, and a trailing `--` comment before a `/-- ... -/`
theorem crediting the *previous* theorem with a property it never cited.
If a row surprises you, suspect the parser before you suspect the proof,
and check the source.

Your step file asks you to add a `--by-property` reporting mode rather
than write a second parser. Keep the dumb heuristic dumb; its value is
that it fails loudly.

## Metrics schema

`verify_runs` / `edit_iterations` / `proof_attempts`. Do not emit
`attempts`: the integration review found it conflated three quantities and
never measured the stop rule it was named for. `proof_attempts` is the one
the three-strikes rule is about.

The shell does not persist between tool calls, so a `START` set in an
earlier call is empty. Write timestamps to a file in `/tmp`, not inside the
worktree — one worker committed one there and needed a second commit to
remove it, and another shipped `wall_seconds: 1788879160` from exactly this
and had to append a correction row.

## Live elaboration gotchas

- `abbrev`, not `def`, for anything instance search must see through.
- Inside a dotted declaration, a bare reference to a same-named function
  resolves to the declaration being defined: `def Comp.apK ... := apK ...`
  silently recursed and cost [sufficient-grade-applicative] real time. It
  fixed it by fully qualifying as `Graded.apK`. Your `traverseK` is a bare
  name, so this should not bite, but qualify if you nest it.
- `Graded g α` lives in `Type (max u v)`, not `Type v`, because `err` holds
  an `Err : Type u`. Ascribe universes on any wrapper abbreviation.
- A bare `pure` in `Tests/*.lean` is ambiguous with Mathlib's `Pure.pure`;
  write `Graded.pure`/`Graded.pureK`. A `#guard` cannot carry a
  `/-- ... -/` doc comment. `#guard` on two `Graded g α` values directly
  has never worked; route through a render-to-`String` function.
- An overlapping instance parameter on a class instance gives
  "synthesized instance not definitionally equal"; [grade-obligations] hit
  this restructuring these very classes, so expect it if you re-shape the
  hierarchy.

## A green build is a silent build

Zero warnings currently. Any warning is yours. Three inherited Mathlib
lint rules are off in `lakefile.toml` because they contradict this project;
do not touch that file.

## Register

The letters carry the author's own editorial register: addressee
`"Steve,"`, signature `"--SMD"`, no em-dashes. Match it in Letter 19 and do
not run a voice tool over any existing letter.

## One thing to be suspicious of

Your step file states a hypothesis and the orchestrator believes it. That
is a reason for care, not confidence: three of this project's better
results were briefs turning out to be wrong, and one step's brief named
the right structure in its first sentence and then set the task against a
different one. Classify each theorem on what its proof actually does. A
single operational law that genuinely needs commutativity or idempotence
refutes the hypothesis, and is worth more than a clean confirmation.
