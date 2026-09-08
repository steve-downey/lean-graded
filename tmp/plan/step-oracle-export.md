# step: oracle-export

## Project context

Lean 4 model of the P3200 / beman.transpose grading design (grade =
`error_set`, a join-semilattice of error types). Integration branch:
`integration/lean-model`. Living doc: `docs/design.md` (by anchor only).
Rules pack: `docs/RULES.md` (always). Each step ends with a letter for the
blog series; see `docs/RULES.md#letter-template`.

## Why

The reason the model exists, from the C++ side, is a table: every law,
its statement, its Lean theorem name, and the pomonoid properties it
depends on — so that (1) the P3200 companion Monad paper can cite which
properties `error_set` supplies and which a future grade must supply,
and (2) the C++ probe harness (std types as probes; no law-checking in
the CRTP machinery, by decision — `docs/design.md#cpp-counterpart`) has
a list of equations to check by example rather than a list someone
remembered. This step produces that table mechanically from the code,
so it cannot drift from the proofs.

## What already exists

Every `Graded/*.lean` module; the `PROPERTY:` tags from
[grade-pomonoid] and [graded-morphism]; `docs/design.md#grade` through
`#representation`.

## The change

### 1. `scripts/laws-inventory.py`

Parse `Graded/*.lean`: for each `theorem <name>`, collect the names of
the tagged property lemmas its proof text mentions (`join_assoc`,
`join_comm`, `join_idem`, `bot_join`, `join_bot`, `le_*`, `join_le`,
`join_mono`, `bot_le`, `rename_join`, `rename_bot`) and map them to
their `PROPERTY:` tag by reading `Graded/Grade.lean` and
`Graded/Morphism.lean`. Emit:

- `docs/laws.md`: a table `theorem | module | properties | C++ law` where
  the C++ column is filled from a small hand-maintained map in the
  script (`bind_pure_left → "and_then(pure(x), f) == f(x)"`, and so on
  for every theorem whose name contains `bind_`, `ap_`, `traverse_`,
  `widen_`, `flatten_`, `rename_`, `sequence_`; unmatched theorems get
  `—`).
- `docs/laws.json`: the same, as a list of objects
  `{theorem, module, properties: [...], cpp: "..."}`.

Mentions-in-proof-text is a heuristic; make it fail loudly (exit 1,
name the theorem) on any theorem whose proof text mentions *no* tagged
lemma and is not on an allow-list of pure-structural theorems
(`map_id`, `map_comp`, `cast_rfl`, …) kept at the top of the script.
Do not make the heuristic smarter than that; a false positive here is a
theorem someone should look at.

### 2. `Makefile`: add `laws` target running the script and `diff`ing
its output against the committed `docs/laws.md`; add it to `all`.

### 3. `docs/design.md#laws-inventory`

The table, transcluded as a link to `docs/laws.md`, plus the
**verdict paragraphs** the paper needs, written from the table:

- which laws needed only unit + associativity (monad; most applicative);
- which needed commutativity (`ap_flip`, `joinAll_perm`, `flatten_comm`);
- which needed idempotence (`foldGrade_cons_ne_nil`, `joinAll_dedup`,
  `traverse_cons`);
- which needed only the order (`widen_*`, `foldGrade_le`, the public
  `traverse` definition);
- the at-most-one-error condition, and the three places it appeared;
- what a *different* grade pomonoid must supply to reuse each part.

Each verdict cites theorem names. Do not editorialize beyond the table.

### 4. The probe list

`docs/probe-harness.md`: for each row with a C++ law, the equation in
C++ syntax against `beman::transpose` names as given in
`docs/design.md#cpp-counterpart`, with the note "check by example with
std types; equality is `==` on the carrier after conversion". This is
the input to the C++ side; nothing here runs C++.

### Tests

None new; `make laws` is the check.

### Letter

`blog/letters/oracle-export.org`, title "The table I actually wanted".
"Refused" section: the script's loud failures — which theorems cited
nothing and why. "Back in C++": the table is the paper's appendix and
the probe harness's spec.

## Declared file scope

`scripts/laws-inventory.py`, `Makefile`, `docs/laws.md`,
`docs/laws.json`, `docs/probe-harness.md`, `docs/design.md`
(`#laws-inventory`), `blog/letters/oracle-export.org`.

## Spot checks

```
make laws; echo $?
python3 -c "import json;d=json.load(open('docs/laws.json'));print(len(d), sum(1 for r in d if 'idempotent' in r['properties']))"
```

## Setup

```
cd __MAIN_CHECKOUT__
git worktree add ../wt-oracle-export -b step/oracle-export integration/lean-model
cd ../wt-oracle-export
ln -s __MAIN_CHECKOUT__/.lake .lake 2>/dev/null || true   # reuse the Mathlib cache; if Lake objects, run 'lake exe cache get' here instead
START=$(date +%s)
```

## Verify GREEN baseline

```
make verify > /dev/null; echo verify=$?      # must be 0
make nosorry; echo nosorry=$?                # must be 0
```
If either is non-zero before you change anything, stop: `blocked-oracle-export.md`
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
oracle-export: mechanical law inventory with pomonoid properties; C++ probe list

Produces the table the model exists for: every theorem, the pomonoid
properties its proof cited, and the C++ equation it corresponds to,
generated from the source so it cannot drift. The verdict paragraphs
are the input to the P3200 companion paper; the probe list is the
input to the C++ test harness.
MSG
cd __MAIN_CHECKOUT__
git checkout integration/lean-model
git merge --no-ff step/oracle-export -m "merge step/oracle-export [oracle-export]"
```

## Record measurements

Before cleanup, from the worktree (so `build.log` and the diff still exist):

```
END=$(date +%s)
cd ../wt-oracle-export
printf '%s\n' '{"step":"oracle-export","lane":null,"outcome":"green","wall_seconds":'"$((END-START))"',"attempts":<n>,"verify":{"command":"make verify","exit_code":0,"wall_seconds":'"$((V1-V0))"',"log_bytes":'"$(wc -c < build.log)"',"summary_lines_read":20},"diff":'"$(git diff --shortstat integration/lean-model~1...step/oracle-export | awk '{printf "{\"files_changed\":%d,\"insertions\":%d,\"deletions\":%d}",$1,$4,$6}')"',"out_of_scope":[],"note":""}' >> __MAIN_CHECKOUT__/tmp/plan/metrics.jsonl
```
Fill `attempts` honestly (a blocked attempt is also a row, with
`"outcome":"blocked"`, appended before cleanup). List any out-of-scope file.

## Cleanup

```
cd __MAIN_CHECKOUT__
git worktree remove --force ../wt-oracle-export
git branch -d step/oracle-export
```

## Handoff

Mark `oracle-export` done in `tmp/plan/checklist.md`. Read
`tmp/plan/step-blog-series-edit.md`. Write `tmp/plan/handoff-blog-series-edit.md` fresh, per
the contract in `AGENT-PROMPT.md`.
