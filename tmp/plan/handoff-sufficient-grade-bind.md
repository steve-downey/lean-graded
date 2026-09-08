# handoff → sufficient-grade-bind

Written by the orchestrator. This step opens a follow-up run planned after
the integration review, so there is no predecessor step to have written it.

Goal and merge criterion: fixed by `step-sufficient-grade-bind.md`.

## The tree you are branching from

All 18 steps of the first run are done and merged on
`integration/lean-model`. `make all`
(`verify nosorry letters laws`) exits 0 with **zero build warnings**, and
the working tree is clean. 146 theorems across 15 `Graded/*.lean` modules.

Nothing you depend on has moved: `Graded/Monad.lean` (`bind`, `pure`, the
five laws, and — note the location — `cast_ok`/`cast_err`/`cast_widen`,
which live there rather than in `Carrier.lean`), `Graded/Widen.lean`
(`widen`, `widen_irrel`, `widen_widen`, `widen_map`, `widen_cast`,
`fromEmpty`, `fromEmpty_eq_ok`), `Graded/Carrier.lean` (`Graded`, `map`,
`cast`, `cast_rfl`, `cast_cast`, `emptyEquiv`), `Graded/Grade.lean` (all
thirteen named lemmas).

## `make laws` will fail until you regenerate, and that is not a bug

`docs/laws.md` and `docs/laws.json` are generated from `Graded/*.lean` by
`scripts/laws-inventory.py`, and `make laws` regenerates and then
`git diff --exit-code`s them. Adding theorems therefore turns `make laws`
red until you run `python3 scripts/laws-inventory.py` and commit the
result. Verified behaviour, not a wrinkle: a source change that alters the
table and is not regenerated fails the check, which is the point.

Two things about that script you should know rather than discover. Its
property attribution is a deliberately dumb mentions-in-proof-text
heuristic, and it exits 1 naming any theorem that cites no tagged property
and is not on its `ALLOWLIST`. **Your `bindK`/`pureK` reduction lemmas and
the bridge theorem will almost certainly trip it**, because they cite
`widen`/`Grade.le_*` rather than a tagged property lemma, or nothing at
all. Add them to `ALLOWLIST` with a one-line reason each, the way the 30
existing entries are documented. Do not widen the allow-list to cover
anything you have not individually justified — an earlier step's whole
value was refusing to do that.

## Metrics schema changed for this run

The integration review found `attempts` conflated three quantities and
never measured the stop rule it was named for. Your step file specifies
`verify_runs` / `edit_iterations` / `proof_attempts`. Use those; do not
emit `attempts`. `proof_attempts` is the one the three-strikes halt rule is
actually about.

Do not fabricate `wall_seconds`: the shell does not persist between tool
calls, so `START` from an earlier call is empty. Write timestamps to a file
in `/tmp` — not inside the worktree, where one worker committed one and
needed a second commit to remove it. Another shipped
`wall_seconds: 1788879160` from exactly this and had to append a
correction row.

## Elaboration gotchas that are still live after eighteen steps

- A bare `pure` in `Tests/*.lean` or `Examples/*.lean` is ambiguous
  between `Graded.pure` and Mathlib's `Pure.pure`. Write `Graded.pure`
  explicitly there. Inside `namespace Graded` it resolves.
- `pure`/`Grade.bot` with no other `Graded`-typed argument nearby leaves
  `DecidableEq Err` stuck ("typeclass instance problem is stuck"). Fix
  with a full type ascription at the use site. `pureK`'s tests are exactly
  the shape that hits this.
- `#guard`/`=` comparing two `Graded g α` values directly has never worked
  in this project. Route through a render-to-`String` function; every
  consumer has its own (`renderN`, `renderSum`, `renderPair`,
  `renderNats`, `renderTuple`, `renderCompList`). Write yours.
- A `#guard` cannot carry a `/-- ... -/` doc comment — it is a parse
  error, not a lint. Use a plain `--`.
- `abbrev`, not `def`, for anything instance search must see through. A
  plain `def` is opaque to it; this cost `Canonical.lean` a rebuild and
  `ComposeApp.lean` was corrected pre-emptively.
- Inside a dotted declaration, a bare reference to a same-named function
  resolves to the declaration being defined, not the one you meant:
  `def Comp.map (f) := map (map f)` silently recursed. If you name
  anything `Sufficient.bindK`-style rather than bare `bindK`, qualify
  inner references fully.
- `Graded g α` lives in `Type (max u v)`, not `Type v`, because `err`
  holds an `Err : Type u`. Ascribe universes explicitly on any wrapper
  abbreviation. `Graded/Compose.lean` pins its payloads to `Type u` for
  this reason.
- `cases h : e with` substitutes `e` throughout the goal; do not add a
  redundant `rw [h]`. But `cases h : f a` does **not** reach an occurrence
  of `f a` under a lambda whose binder shadows `a` — reduce with your
  `bindK_ok` lemma first, then case. That is precisely where the
  orchestrator's spike of `bindK_assoc` stalled, and it is the reason your
  step file insists on reduction lemmas before laws.

## A green build is a silent build

`lake build` completes with zero warnings. Any warning is yours; read it.
Three inherited Mathlib lint rules are off in `lakefile.toml`
(`style.header`, `hashCommand`, `dupNamespace`) because they contradict
this project — `hashCommand` forbids the `#guard` that `docs/RULES.md`
requires. Do not touch `lakefile.toml`; that is an "ask".

## Staging

The working tree in the main checkout is clean and should stay that way.
Stage your own files by name there; `git add -A` is fine inside your
worktree only. The letters under `blog/letters/` carry the author's own
editorial register (addressee `"Steve,"`, signature `"--SMD"`, no
em-dashes) — match it in Letter 17, and do not reintroduce em-dashes.

## What your verdict gates

`step-sufficient-grade-applicative.md` does not run if your measurement
says the cast-free layer is not worth extending. Put the verdict in the
first line of your outbound handoff either way. "Not worth it" is a
completed question and a good outcome; the trap to avoid is a verdict
shaped by wanting the next step to happen.
