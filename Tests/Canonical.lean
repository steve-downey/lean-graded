import Graded.Canonical

/-! Instantiate `Graded.Canonical`'s theorems at a concrete `Err`. Unlike
    every earlier `Tests/*.lean`, this one cannot reuse `Examples.Validation.E`
    (`deriving DecidableEq, Repr` only) — `Canon` needs `[LinearOrder Err]`,
    so this module's `Err` needs an order, given by an explicit embedding
    into `Nat` (`docs/RULES.md#tests` allows this in place of the default
    `E`). -/

namespace Tests

open Graded List

/-- A three-error universe, ordered by an explicit embedding into `Nat`
    rather than by `deriving Ord` — the embedding is the more direct proof
    obligation for a three-constructor type. `DecidableEq` is deliberately
    *not* derived here: deriving it separately from the `LinearOrder`
    instance below would give `CE` two different `DecidableEq` instances
    (the derived one and `LinearOrder.toDecidableEq`) that are not
    syntactically the same instance, which `Finset`/`Grade` operations
    then trip over. Getting `DecidableEq` from `LinearOrder` alone avoids
    the diamond. -/
inductive CE | parse | range | io
  deriving Repr

private def CE.toNat : CE → Nat
  | .parse => 0
  | .range => 1
  | .io => 2

private theorem CE.toNat_injective : Function.Injective CE.toNat := by
  intro a b h
  cases a <;> cases b <;> simp_all [CE.toNat]

instance : LinearOrder CE := LinearOrder.lift' CE.toNat CE.toNat_injective

-- `canonEquiv` sorts `{CE.range, CE.parse}` by the order `toNat` induces —
-- `parse` (0) before `range` (1) — computed by `#guard`, not merely
-- asserted.
#guard (canonEquiv ({CE.range, CE.parse} : Grade CE)).val = [CE.parse, CE.range]

-- Round-trip: forgetting the order and re-sorting recovers the original
-- set (`Canon.ofFinset_toFinset`'s concrete instance, the other direction
-- of `Canon.toFinset_ofFinset` above).
#guard Canon.toFinset (Canon.ofFinset ({CE.range, CE.parse} : Grade CE)) =
  ({CE.range, CE.parse} : Grade CE)

-- `canon_perm`: two different textual orderings of the same pair of error
-- kinds sort to the same canonical representative — the concrete instance
-- of "`error_set<A,B>` is `error_set<B,A>`" this codebase's `decide`/
-- `#guard` convention (`docs/RULES.md#tests`) asks for.
#guard Canon.ofList ([CE.range, CE.parse] : List CE) =
  Canon.ofList ([CE.parse, CE.range] : List CE)

example (h : ([CE.range, CE.parse] : List CE) ~ [CE.parse, CE.range]) :
    Canon.ofList [CE.range, CE.parse] = Canon.ofList [CE.parse, CE.range] :=
  Canon.canon_perm h

-- `canonEquiv_union`: the joined grade's canonical representative is the
-- (round-trip) union of each grade's own representative.
#guard canonEquiv (Grade.join ({CE.parse} : Grade CE) ({CE.range} : Grade CE)) =
  Canon.union (canonEquiv ({CE.parse} : Grade CE)) (canonEquiv ({CE.range} : Grade CE))

-- ---------------------------------------------------------------------
-- The round-trips and the union transport, at **two distinct nonempty
-- grades** written in the order the sort has to fix — `{range, parse}`
-- sorts to `[parse, range]`, so a `canonEquiv` that ignored its
-- `LinearOrder` would fail these rather than pass them.

example (s : Finset CE) : Canon.toFinset (Canon.ofFinset s) = s :=
  Canon.toFinset_ofFinset s

example (c : Canon CE) : Canon.ofFinset (Canon.toFinset c) = c :=
  Canon.ofFinset_toFinset c

example : canonEquiv (Grade.join ({CE.range} : Grade CE) {CE.parse})
    = Canon.union (canonEquiv ({CE.range} : Grade CE)) (canonEquiv ({CE.parse} : Grade CE)) :=
  canonEquiv_union {CE.range} {CE.parse}

#guard Canon.toFinset (Canon.ofFinset ({CE.range, CE.parse} : Grade CE))
  = ({CE.range, CE.parse} : Grade CE)
#guard (Canon.union (canonEquiv ({CE.range} : Grade CE))
  (canonEquiv ({CE.parse} : Grade CE))).val = [CE.parse, CE.range]

end Tests
