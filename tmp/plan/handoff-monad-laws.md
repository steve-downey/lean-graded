# handoff → monad-laws

Goal and merge criterion: fixed by `step-monad-laws.md`.

## `Graded/Widen.lean` now exists — use it, don't reinvent it

`widen (h : g ⊆ g') : Graded g α → Graded g' α` and five theorems are
already in place, exactly under the names your step file's proof sketch
expects: `widen_refl`, `widen_widen`, `widen_map`, `widen_irrel`,
`widen_cast`. All five are proved by `rfl` or `subst; rfl` — none needed a
`grind` loop, so they reduce completely and are cheap `simp` lemmas if you
need them for `bind_assoc` (your own step file's hint — `cases x` then
`simp [cast, widen_widen, widen_irrel]` — should find them with no extra
setup). `fromEmpty`/`fromEmpty_eq_ok` also exist but you probably don't
need them; `pure` is defined directly as `.ok a`, not routed through
`fromEmpty`.

## `Grade.le_refl'` is not point-free — your `bind_widen` sketch needs a fix

`Graded/Grade.lean` declares `theorem le_refl' (g : Grade Err) : g ⊆ g`
with `g` **explicit**. Your step file's stated theorem —

```
bind_widen : bind (widen h₁ x) f = widen (Grade.join_mono h₁ le_refl') (bind x f)
```

— will not elaborate as written: `le_refl'` alone is a function, not a
proof term. You'll need `Grade.le_refl' h` (naming the grade of `f`'s
domain) or `Grade.le_refl' _` and let unification fill it in. Same shape
of mistake as `cast`'s non-point-free form that bit the previous step;
this is the same lesson applied to a different lemma.

## `Examples/Validation.lean` already has the three-stage shape you need

This step's consumer section says "the three-stage version with nested
`bind`" as if a third stage already exists — it does. `logIt : Nat →
Graded ({E.io} : Grade E) Unit := .ok ()` was added in
[subsumption-widen], right after `render`. Use it for your nested-`bind`
three-stage example; don't declare a fourth stage or a second `logIt`.

Immediately after `logIt` there is a `#guard` (no preceding docstring —
see below) that widens `parseNat`'s failure into the three-error union
grade and checks it against the same failure built directly there. It
depends only on `parseNat`, `widen`, and `E` — not on `validate` — so it
is unaffected by your rewrite of the `-- REPLACED-BY: bind` block. Leave
it in place; your edits belong entirely inside `validate`'s definition
(and wherever you add the three-stage nested-`bind` version).

## A `#guard` cannot carry a `/-- ... -/` doc comment

I hit this directly: `#guard` is not a named declaration, so a doc-string
immediately before one is a parse error (`unexpected token '#guard';
expected 'lemma'`), not a lint warning — it fails the build outright. Use
a plain `--` comment instead. You'll likely write several `#guard`s
(`docs/RULES.md` requires at least one per test file, and your own step
asks you to compare `#eval` outputs with `#guard`), so this will come up.

## Builds are still warning-free

`lake build` on `integration/lean-model` after the subsumption-widen
merge completes with zero warnings. If you see one, you introduced it —
worth reading rather than stepping around.

## `variable` lines don't cross file boundaries (same as the graded-carrier → subsumption-widen handoff said)

`Graded/Widen.lean` re-declares `variable {Err : Type u} [DecidableEq
Err]` and `variable {g g' g'' : Grade Err} {α β : Type v}` at its top,
copied from `Graded/Carrier.lean` — they don't carry over via import.
`Graded/Monad.lean` will need its own copy of whichever of these (plus
any grade variables for `bind`'s two arguments) it uses. Skipping this
gives a cryptic metavariable/typeclass-stuck error pointing at an
unrelated line, not an "unbound identifier" error — check for a missing
`variable` line first if you see that.

## Merge commit

`step/subsumption-widen` merged into `integration/lean-model` at
`689d9fd` (`--no-ff`). `integration/lean-model` is GREEN (`make verify`,
`make nosorry`, `make letters` all exit 0) as of that commit.
