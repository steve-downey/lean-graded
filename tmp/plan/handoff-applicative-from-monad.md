# handoff → applicative-from-monad

Goal and merge criterion: fixed by `step-applicative-from-monad.md`.

## `Graded/Monad.lean` now exists — `pure`, `bind`, and three transport
lemmas you'll want, not just the five named laws

`pure`, `bind`, `bind_pure_left`, `bind_pure_right`, `bind_assoc`,
`bind_map`, `bind_widen` are all in place, `import Graded.Monad` to get
them (it's already wired into `Graded.lean`). More useful for *you*:
three small generic lemmas sit right above the named laws in that file —

```lean
theorem cast_ok (e : g = g') (a : α) :
    cast e (Graded.ok a : Graded g α) = Graded.ok a := by subst e; rfl
theorem cast_err (e : g = g') (er : Err) (he : er ∈ g) :
    cast e (Graded.err er he : Graded g α) = Graded.err er (e ▸ he) := by subst e; rfl
theorem cast_widen (h₁ : g ⊆ g') (e : g' = g'') (x : Graded g α) :
    cast e (widen h₁ x) = widen (e ▸ h₁) x := by subst e; rfl
```

These closed every `cast` that ever met a constructor or a `widen` across
all five monad laws. `ap`'s definition sketch in your step file ends with
`|> cast (by ...)`, and the four `ap_*` laws all have `cast _`
placeholders — reach for these three first before writing a bespoke
proof; `ap` is built from nested `bind`/`pure`, so its casts have the
same shape as `bind_map`'s (a `join _ Grade.bot` collapsing to plain `g`).

## Cast direction convention (recorded at `docs/design.md#monad`)

Every cast-bearing law states `cast (Grade.<lemma> …) (<compound
bind/join expression>) = <simpler expression>`, using each pomonoid
lemma in the direction it's already stated in `Graded/Grade.lean` —
never `.symm`. This was a free choice (the reverse direction typechecks
too) but it means no law or use site ever needed a `.symm`. Follow the
same convention for `ap_pure_id`, `ap_comp`, `ap_pure_pure`,
`ap_interchange`: cast the side whose grade is the visible `join`
expression down to the tidy one.

## `show` that changes the goal now warns; the build must stay
warning-free

Lean's `show` tactic linter flags any use that actually changes the
goal ("The `show` tactic should only be used to indicate intermediate
goal states for readability... use `change` instead"). I hit this
repeatedly restating `bind`'s reduced form by hand. Use `change`, not
`show`, whenever you're spelling out what `ap`/`bind`/`pure` unfold to.

## `cases h : e with` *does* substitute `e` everywhere in the goal

I initially assumed it only added the equation hypothesis without
touching the goal; it actually replaces every literal occurrence of `e`
with the matched constructor, same as plain `cases e`. Relevant if you
case on a sub-expression like `f a` or `k b` inside an `ap`/`bind` proof
— don't add a redundant `rw [h]` afterward, the substitution already
happened.

## Grade lemmas with explicit grade arguments need them spelled out

`Grade.le_join_left`, `Grade.le_join_right`, `Grade.bot_join`,
`Grade.join_bot`, `Grade.le_refl'` all take their `Grade` arguments
*explicit* (not implicit) — writing `Grade.le_join_right` bare, or
`Grade.le_refl'` bare, doesn't elaborate; you must write
`Grade.le_join_right g h`, `Grade.le_refl' h`, etc. (already flagged for
`le_refl'` in the subsumption-widen → monad-laws handoff; it applies to
all of these). `bind`'s own definition in `Graded/Monad.lean` supplies
them this way — copy that pattern for `ap`.

## `#guard` on a bare `Graded g α = Graded g α` equality can fail to
elaborate even when both sides are honestly defeq

I hit "type mismatch: ... has type Prop but is expected to have type
Bool" and then, after wrapping in `decide`, "failed to synthesize
instance of type class Decidable (...)" when comparing `bind (parseNat
"42") checkRange` directly against a `Graded.ok 42 : Graded
({E.parse,E.range}) Nat` literal — even though that exact defeq (`join
{parse} {range} = {parse,range}` reduces all the way, concretely) is
what lets `validate`'s type ascription itself typecheck with no cast.
Route this kind of `#guard` through a `render`-style function to `String`
instead (String equality has no such trouble) rather than comparing two
`Graded` values whose grades are written differently even if defeq.

## `Grade.join {a} {b}` and the literal `{a, b}` Finset notation are
defeq for concrete decidable-eq elements

`validate : String → Graded ({E.parse, E.range} : Grade E) Nat := bind
(parseNat s) checkRange` typechecks with no `cast` at that boundary,
even though `bind`'s inferred return type is `Graded (Grade.join
{E.parse} {E.range}) Nat` — the two Finset expressions reduce to the
same underlying representation for concrete literals. Don't assume this
in general (it's why the monad laws still need `cast` for *variable*
grades `g`, `h`), but it means your consumer section's `map2 (· + ·)
(parseNat s₁) (parseNat s₂)` can likely keep a literal-set return type
with no extra cast at the definition boundary.

## Merge commit

`step/monad-laws` merged into `integration/lean-model` at
`54dd674` (`--no-ff`). `integration/lean-model` is GREEN (`make verify`,
`make nosorry`, `make letters` all exit 0) as of that commit.
