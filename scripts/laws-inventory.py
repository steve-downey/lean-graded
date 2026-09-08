#!/usr/bin/env python3
"""Mechanical law inventory for the Lean model of graded Transpose.

Parses every `theorem <name>` declared in `Graded/*.lean`, and for each one
collects which of a small, fixed vocabulary of pomonoid-property lemma names
its declaration text (docstring + signature + proof, taken together — not
just the tactic block) mentions. Each vocabulary name is mapped to a
PROPERTY tag by reading the `/-- PROPERTY: <tag> -/` comments that precede
lemmas in `Graded/Grade.lean` and `Graded/Morphism.lean`, plus a small,
explicit, hand-checked supplement (see ORDER_SUPPLEMENT below) for the
handful of order-related lemmas in `Graded/Grade.lean` that state real
consequences of the order (`join_le`, `join_mono`, `bot_le`,
`le_join_left`, `le_join_right`) but were not given a literal PROPERTY
docstring there ([grade-pomonoid] tagged only the four defining
inequalities `le_refl'`/`le_trans'` that way).

This is deliberately a *dumb* heuristic: a theorem whose declaration text
mentions none of the vocabulary names, and is not on the small ALLOWLIST of
genuinely pure-structural theorems below, is something a human should look
at — the script names it and exits 1. It does not try to see through a
`simp only [someDef]` unfold to whatever property `someDef`'s own body
cites, and it does not distinguish two theorems that happen to share a bare
name in different namespaces (`Graded.Grade.join_le` vs the generic
`Graded.join_le` in `Graded/Obligations.lean`) — rows are kept apart by
`module`, not merged by name, but a *mention* of the bare name inside some
third theorem's proof is credited to the tag regardless of which of the two
same-named lemmas was actually meant. See `blog/letters/oracle-export.org`
for what this cost in practice.
"""

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GRADED_DIR = ROOT / "Graded"

# ---------------------------------------------------------------------------
# The fixed search vocabulary (from the step brief, verbatim) plus the two
# `le_*` names that are actually spelled out in `Graded/Grade.lean`.
VOCAB = [
    "join_assoc",
    "join_comm",
    "join_idem",
    "bot_join",
    "join_bot",
    "le_refl'",
    "le_trans'",
    "le_join_left",
    "le_join_right",
    "join_le",
    "join_mono",
    "bot_le",
    "rename_join",
    "rename_bot",
]

# Untagged consequences of the order in `Graded/Grade.lean` — no literal
# `PROPERTY:` docstring, but plainly order facts (`g ⊆ join g h`, `join g h
# ⊆ k` from two one-sided bounds, `∅ ⊆ g`), documented as "(order)" in the
# prose of every module that cites them (`Widen`, `Monad`, `Compose`,
# `Traverse`). Kept separate from the PROPERTY-tag scan below, and small
# enough to read at a glance and check against the source by hand.
ORDER_SUPPLEMENT = {
    "le_join_left": "order",
    "le_join_right": "order",
    "join_le": "order",
    "join_mono": "order",
    "bot_le": "order",
}

# Theorems the script flagged that a human (this step's worker) then looked
# at and judged safe to allow-list — every one individually, never as a
# blanket "reduction lemma" pass. Two, and only two, reasons are accepted;
# each entry says which. Neither reason is "it's inconvenient to fix" and
# neither hypothesis is ever strengthened to make a proof easier — that is
# a `blocked-`/`amendment-` situation, not an allow-list entry. Full
# reasoning for every entry is in `blog/letters/oracle-export.org`'s
# "What the checker refused" section; this dict's value is the one-line
# version, kept next to the code it excuses so the two cannot drift apart.
#
#   structural — no pomonoid property is at stake even in principle: the
#     statement never puts two grades in a `join` together (an `ok`/`ok`
#     reduction case, a naturality fact at a single fixed grade, a
#     `Finset.sort`/`Finset.image` fact with no `Grade.join`/`Grade.bot` in
#     sight, a fact about which element of a list comes first).
#   delegates — the proof's only work is `rw`/`cases`/`exact` into another
#     *already-tabulated* theorem (named in the reason) that itself cites
#     the property directly; the property is real, and it is on that row,
#     not invented here.
ALLOWLIST = {
    # --- structural -----------------------------------------------------
    "map_id": "structural: functor law, no grade in sight",
    "map_comp": "structural: functor law, no grade in sight",
    "cast_rfl": "structural: generic cast transport",
    "cast_cast": "structural: generic cast transport",
    "cast_ok": "structural: generic cast transport, ok case",
    "cast_err": "structural: generic cast transport, err case",
    "cast_errs": "structural: generic cast transport, Accum errs case",
    "cast_widen": "structural: cast commutes with widen, no join",
    "widen_cast": "structural: widen commutes with cast, no join",
    "widen_map": "structural: widen commutes with map, no join",
    "widen_irrel": "structural: proof-irrelevance of the inclusion witness",
    "Comp.map_id": "structural: functor law, no grade in sight",
    "Comp.map_comp": "structural: functor law, no grade in sight",
    "ap_ok_ok": "structural: ok/ok case, function applied, no error, no join",
    "apFlipped_ok_ok": "structural: ok/ok case, no join",
    "Comp.ap_ok_ok": "structural: ok/ok case, no join",
    "apF_ok_ok": "structural: ok/ok case; join_idem is needed only to state "
        "apF's type, not to prove this reduction (cast_ok discharges any "
        "witness of g=g alike)",
    "bindF_ok": "structural: reduction lemma, documented as such at its own "
        "definition site; unfolds to widen_refl via proof irrelevance",
    "bindF_err": "structural: reduction lemma, documented as such",
    "apF_err_left": "structural: reduction lemma; delegates to ap_err_left "
        "(order) plus cast_err, same non-need for join_idem as apF_ok_ok",
    "apF_ok_err": "structural: reduction lemma, same reasoning as apF_err_left",
    "rename_ok": "structural: rename threads a function, no grade arithmetic",
    "rename_err": "structural: rename threads a function, no grade arithmetic",
    "rename_map": "structural: naturality at one grade, no join",
    "rename_widen": "structural: naturality at one grade, no join",
    "rename_cast": "structural: naturality at one grade, no join",
    "rename_toGraded": "structural: Accum's rename naturality, no join "
        "(qualifies as Graded.Accum.rename_toGraded)",
    "toGraded_ok": "structural: definitional unfold",
    "toGraded_errs": "structural: definitional unfold",
    "toGraded_grade": "structural: which list element is first, not a "
        "pomonoid fact — the at-most-one-error hypothesis is recorded but "
        "not load-bearing here (see toGraded_grade')",
    "toGraded_grade'": "structural: same list-order fact, unconditionally",
    "sequence_nil": "structural: definitional unfold",
    "sequence_cons": "structural: definitional unfold",
    "joinAll_nil": "structural: definitional unfold",
    "joinAll_cons": "structural: definitional unfold",
    "foldGrade_nil": "structural: definitional unfold",
    "foldGrade_cons": "structural: definitional unfold",
    "foldG_nil": "structural: definitional unfold",
    "foldG_cons": "structural: definitional unfold",
    "joinAllG_nil": "structural: definitional unfold",
    "joinAllG_cons": "structural: definitional unfold",
    "pureF_eq_ok": "structural: definitional unfold",
    "fromEmpty_eq_ok": "structural: definitional unfold",
    "flatten_eq_bind_id": "structural: definitional identity between flatten and bind id",
    "flatten_map": "structural: naturality in the payload, no join",
    "canonEquiv_bot": "structural: definitional unfold at bot",
    "canonEquiv_union": "structural: Canon.union is *defined* by round-tripping "
        "through Finset union; the proof only unfolds that definition and "
        "Grade.join's own, never re-derives a join property",
    "join_eq_right_of_le": "structural: primitive order fact proved directly "
        "from Finset.union_eq_right, same footing as le_refl'/le_trans' — a "
        "defining fact does not cite itself",
    "toFinset_ofFinset": "structural: Finset.sort/Finset.toFinset round-trip, no Grade.join/bot",
    "ofFinset_toFinset": "structural: Finset.sort/Finset.toFinset round-trip, no Grade.join/bot",
    "mem_rename": "structural: Finset.image membership transport, no Grade.join/bot",
    "rename_mono": "structural: Finset.image_subset_image directly, no named Grade lemma",
    "map_emptyEquiv": "structural: naturality at grade bot only — no join is "
        "even expressible at bot",
    "errs_eq_of_list_eq": "structural: list-equality-implies-Accum-equality, not a pomonoid fact",
    "notMonad": "structural: a non-existence argument about function extensionality on an uninhabited domain",
    "nat_not_idem": "structural: 1+1≠1 on Nat, arithmetic, not a Grade fact",
    "sumEquiv_pureF": "structural: Sum correspondence at pure, no join",
    # --- delegates --------------------------------------------------------
    "canon_perm": "delegates to Graded.Tuple.joinAll_perm (commutative, associative); "
        "no independent proof content of its own",
    "traverseComp_eq": "delegates to Comp.traverseComp_cons and traverse_cons "
        "(both idempotent); the composition law's own proof only case-splits "
        "on ok/err and rewrites through those two",
    "flatten_ap": "delegates to Comp.grade_reassoc (associative, commutative) "
        "for the grade equation; the value-level case split cites no "
        "property of its own beyond that cast — the headline finding, see "
        "the letter",
    "traverse_cons_ok_ok": "delegates to traverse_cons (idempotent)",
    "traverse_map": "delegates to traverse_cons (idempotent), twice, by induction",
    "traverse_length": "delegates to the traverse_cons_* reduction lemmas, "
        "themselves delegating to traverse_cons (idempotent)",
    "traverse_nil": "delegates to fromEmpty_eq_ok (structural)",
    "traverse_rename": "the join_idem cast this needs (module docstring: "
        "\"the casts from rename_cast/rename_map2/Grade.join_idem\") is "
        "cancelled by proof irrelevance inside the induction step, not by "
        "an explicit rewrite — so the token never appears, by construction",
    "joinAll_dedup": "delegates to join_mem_eq (associative, commutative, "
        "idempotent) — that theorem's own docstring says dedup is exactly "
        "where join_idem is spent",
    "bindF_pure_left": "delegates to bindF_ok (structural)",
    "bindF_pure_right": "delegates to bindF_ok/bindF_err (structural)",
    "bindF_assoc": "delegates to bindF_ok/bindF_err (structural); at a fixed "
        "grade both sides reduce to the same term before associativity "
        "could matter — see the theorem's own docstring",
    "apF_pure_id": "delegates to apF_ok_ok/apF_ok_err (structural)",
    "apF_pure_pure": "delegates to apF_ok_ok (structural) directly",
    "apF_interchange": "delegates to apF_ok_ok/apF_err_left/apF_ok_err (structural)",
    "apF_comp": "delegates to apF_ok_ok/apF_ok_err/apF_err_left (structural)",
    "traverse_fromEmpty_map": "delegates to traverse_map and traverse_fromEmpty "
        "(both already tabulated); costs nothing beyond citing both, per its own docstring",
    "sumEquiv_bindF": "delegates to bindF_ok/bindF_err (structural)",
}

PROPERTY_TAG_RE = re.compile(
    r"/--\s*PROPERTY:\s*([a-zA-Z]+)\s*-/\s*\n\s*theorem\s+([A-Za-z_][A-Za-z0-9_'.]*)"
)

THEOREM_RE = re.compile(
    r"^theorem\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.MULTILINE
)

# Any line starting one of these keywords at column 0, or a free-floating
# `/-!` module-doc block, or this codebase's own `-- ----...` section
# separator, ends a declaration's text and starts the next one — used to
# carve each theorem's own signature+proof out of the whole file without
# tracking brace/tactic nesting. `/-!` and the dash separator matter
# because both are used here purely as *floating* section prose, never as
# a specific declaration's docstring (that is always `/--`, immediately
# adjacent) — without treating them as boundaries too, a floating comment
# sitting between two theorems is swallowed into the *preceding* theorem's
# scanned text and can credit it with a mention that is actually about
# something else entirely (this bit `Ungraded.apF_comp`, which otherwise
# absorbed a trailing comment's mention of `Grade.join_comm` describing a
# different theorem, `ap_flip`).
# `/--` is included too: it always opens the *next* declaration's own
# docstring (never the previous one's trailing remark), so without it here
# a theorem's chunk runs on into the following theorem's docstring and can
# credit the wrong theorem with a mention that is actually about its
# neighbour (this bit `bindF_pure_right`/`bindF_assoc`/`apF_interchange` in
# `Graded/Ungraded.lean`, each absorbing the *next* theorem's docstring).
BOUNDARY_RE = re.compile(
    r"^(theorem|def|instance|abbrev|structure|class|namespace|end|section|"
    r"variable|open|inductive)\b|^/-!|^/--|^-- -{3,}",
    re.MULTILINE,
)


def build_property_map():
    """Read Graded/Grade.lean and Graded/Morphism.lean for literal
    `/-- PROPERTY: X -/` tags, then add the small order supplement."""
    tags = {}
    for fname in ("Grade.lean", "Morphism.lean"):
        text = (GRADED_DIR / fname).read_text()
        for m in PROPERTY_TAG_RE.finditer(text):
            prop, name = m.group(1), m.group(2)
            tags[name] = prop
    for name, prop in ORDER_SUPPLEMENT.items():
        tags.setdefault(name, prop)
    missing = [v for v in VOCAB if v not in tags]
    if missing:
        sys.exit(
            "laws-inventory: internal error — vocabulary name(s) with no "
            f"property mapping: {missing}"
        )
    return tags


def theorem_chunks(path: Path):
    """Yield (name, chunk_text) for every top-level `theorem` in `path`,
    where chunk_text runs from the `theorem` line itself up to (not
    including) the next declaration boundary — the theorem's own
    signature and full proof, deliberately *not* any preceding docstring
    (RULES.md's discipline is about what the *proof* cites, and every
    finding this script needed was already visible in the statement or
    the tactic block; see the letter for the one file-level chunking bug
    this asymmetry sidesteps)."""
    text = path.read_text()
    boundaries = [m.start() for m in BOUNDARY_RE.finditer(text)] + [len(text)]
    theorem_starts = {m.start(): m.group(1) for m in THEOREM_RE.finditer(text)}
    for i, start in enumerate(boundaries[:-1]):
        if start not in theorem_starts:
            continue
        name = theorem_starts[start]
        chunk_end = boundaries[i + 1]
        yield name, text[start:chunk_end]


# Lean identifiers here can end in `'` (`le_refl'`, `le_trans'`), which is
# not a `\w` character, so a plain `\b...\b` regex boundary never fires
# after it (both the apostrophe and whatever follows — space, `)`, `.` —
# are "non-word", and `\b` needs one side word and one side not). Treat `'`
# as part of the identifier-character class for boundary purposes instead.
_ID_CHARS = r"A-Za-z0-9_'"


def _mention_re(name: str) -> re.Pattern:
    return re.compile(
        rf"(?<![{_ID_CHARS}]){re.escape(name)}(?![{_ID_CHARS}])"
    )


def mentioned_properties(chunk: str, property_of: dict):
    found = set()
    props = set()
    for name in VOCAB:
        if _mention_re(name).search(chunk):
            found.add(name)
            props.add(property_of[name])
    return found, props


# ---------------------------------------------------------------------------
# The C++ law column: a small, hand-maintained map from theorem name to the
# `beman::transpose`-flavoured equation it corresponds to. Unmatched
# theorems get "—". Keyed by the name exactly as captured (so a
# `Comp.`/`Accum.`-qualified name is a distinct key from its bare
# counterpart in another module).
CPP_LAW = {
    # --- monad ---
    "bind_pure_left": "and_then(pure(x), f) == f(x)",
    "bind_pure_right": "and_then(x, pure) == x",
    "bind_assoc": "and_then(and_then(x, f), k) == and_then(x, [=](auto a){ return and_then(f(a), k); })",
    "bind_map": "and_then(x, [=](auto a){ return pure(f(a)); }) == transform(x, f)",
    "bind_widen": "and_then(widen<Es2>(x), f) == widen<Es2 | Fs>(and_then(x, f))",
    # --- applicative (from monad) ---
    "ap_pure_id": "apply(pure(id), x) == x",
    "ap_pure_pure": "apply(pure(f), pure(a)) == pure(f(a))",
    "ap_interchange": "apply(u, pure(a)) == apply(pure([=](auto f){ return f(a); }), u)",
    "ap_comp": "apply(apply(apply(pure(compose), u), v), w) == apply(u, apply(v, w))",
    "ap_flip": "apply(f, x) == apply_flipped(f, x)  // only when at most one side errs",
    # `Graded.Accum`'s `ap_pure_id`/`ap_pure_pure`/`ap_interchange`/`ap_comp`
    # are declared inside `namespace Accum`, so — unlike `Comp.ap_pure_id`
    # below, which dot-qualifies its name explicitly — they are captured
    # under the *same bare name* as `Graded.Applicative`'s own four laws,
    # and this table cannot key them apart (rows stay apart by `module`;
    # the C++ column does not). They share the entries above; the equation
    # shape is the same either way, only the accumulation behaviour on
    # failure differs, which the boolean `==` doesn't distinguish.
    # --- traverse (List) ---
    "traverse_nil": "traverse(f, {}) == pure({})",
    "traverse_cons": "traverse(f, x :: xs) == map2(cons, f(x), traverse(f, xs))",
    "traverse_map": "traverse(f, transform(xs, h)) == traverse(f compose h, xs)",
    "traverse_fromEmpty": "traverse(fromEmpty, xs) == fromEmpty(xs)  // no-fail context is a no-op",
    "traverse_length": "traverse(f, xs).value().size() == xs.size()  // shape preservation",
    "traverse_rename": "transform_error(traverse(f, xs), phi) == traverse(transform_error(f, phi), xs)",
    "traverse_fromEmpty_map": "traverse(fromEmpty compose f, xs) == fromEmpty(transform(xs, f))",
    # --- traverse (Tuple) ---
    "joinAll_perm": "error_set<Es...> == error_set<permutation of Es...>",
    "joinAll_dedup": "error_set<Es..., duplicates removed> == error_set<Es...>",
    "sequence_cons": "transpose(x, xs...) == map2(tuple_cons, x, transpose(xs...))",
    # --- compose (flatten) ---
    "flatten_map": "transform(flatten(x), f) == flatten(transform(transform(x, f)))",
    "flatten_pure_outer": "flatten(pure(y)) == y",
    "flatten_pure_inner": "flatten(transform(x, pure)) == x",
    "flatten_flatten": "flatten(flatten(x)) == flatten(transform(x, flatten))",
    "flatten_widen_outer": "flatten(widen<Es2>(x)) == widen<Es2 | Fs>(flatten(x))",
    "flatten_widen_inner": "flatten(transform(x, widen<Fs2>)) == widen<Es | Fs2>(flatten(x))",
    "flatten_comm": "flatten(x) == flatten(swap(x))  // up to reordering the union's arguments",
    # --- compose-applicative (Comp) ---
    "Comp.ap_pure_id": "apply(pure(id), x) == x  // nested, componentwise",
    "Comp.ap_pure_pure": "apply(pure(f), pure(a)) == pure(f(a))  // nested, componentwise",
    "Comp.ap_interchange": "apply(u, pure(a)) == apply(pure([=](auto f){ return f(a); }), u)  // nested",
    "Comp.ap_comp": "apply(apply(apply(pure(compose), u), v), w) == apply(u, apply(v, w))  // nested",
    "traverseComp_eq": "transpose_nested(transform(f, map(k))) == transform(map(transpose(k)), transpose(f, xs))",
    "flatten_ap": "flatten(apply(ff, xx)) == apply(flatten(ff), flatten(xx))  // one-sided condition only",
    # --- morphisms ---
    "rename_map": "transform_error(transform(x, f), phi) == transform(transform_error(x, phi), f)",
    "rename_widen": "transform_error(widen<Es2>(x), phi) == widen<image of Es2>(transform_error(x, phi))",
    "rename_cast": "transform_error(x, phi) commutes with a same-set grade cast",
    "rename_pure": "transform_error(pure(a), phi) == pure(a)",
    "rename_bind": "transform_error(and_then(x, f), phi) == and_then(transform_error(x, phi), transform_error(_, phi) compose f)",
    "rename_ap": "transform_error(apply(f, x), phi) == apply(transform_error(f, phi), transform_error(x, phi))",
    "rename_map2": "transform_error(map2(k, x, y), phi) == map2(k, transform_error(x, phi), transform_error(y, phi))",
    "Accum.rename_toGraded": "first_error(transform_error(x, phi)) == transform_error(first_error(x), phi)",
    # --- ungraded-baseline (Fixed g) ---
    "bindF_pure_left": "and_then(pure(x), f) == f(x)  // fixed grade, cast-free",
    "bindF_pure_right": "and_then(x, pure) == x  // fixed grade, cast-free",
    "bindF_assoc": "and_then(and_then(x, f), k) == and_then(x, [=](auto a){ return and_then(f(a), k); })  // fixed grade",
    "apF_pure_id": "apply(pure(id), x) == x  // fixed grade, cast-free",
    "apF_pure_pure": "apply(pure(f), pure(a)) == pure(f(a))  // fixed grade, cast-free",
    "apF_interchange": "apply(u, pure(a)) == apply(pure([=](auto f){ return f(a); }), u)  // fixed grade",
    "apF_comp": "apply(apply(apply(pure(compose), u), v), w) == apply(u, apply(v, w))  // fixed grade",
    "sumEquiv_bindF": "and_then(x, f) corresponds to std::expected/variant-style Sum::bind under the Equiv",
}


def cpp_law_for(name: str) -> str:
    return CPP_LAW.get(name, "—")


def main():
    property_of = build_property_map()

    rows = []
    flagged = []
    for path in sorted(GRADED_DIR.glob("*.lean")):
        module = f"Graded/{path.name}"
        for name, chunk in theorem_chunks(path):
            _found, props = mentioned_properties(chunk, property_of)
            row = {
                "theorem": name,
                "module": module,
                "properties": sorted(props),
                "cpp": cpp_law_for(name),
            }
            rows.append(row)
            if not props and name not in ALLOWLIST:
                flagged.append((module, name))

    if flagged:
        sys.stderr.write(
            "laws-inventory: the following theorems cite no tagged pomonoid "
            "property and are not on the allow-list — a human should look "
            "at each:\n"
        )
        for module, name in flagged:
            sys.stderr.write(f"  {module}: {name}\n")
        sys.stderr.write(f"({len(flagged)} theorem(s) flagged)\n")
        sys.exit(1)

    write_outputs(rows)
    print(f"laws-inventory: {len(rows)} theorems tabulated, 0 flagged.")


def write_outputs(rows):
    docs_dir = ROOT / "docs"
    docs_dir.mkdir(exist_ok=True)

    json_path = docs_dir / "laws.json"
    json_path.write_text(json.dumps(rows, indent=2) + "\n")

    md_lines = [
        "# Laws inventory",
        "",
        "Generated by `scripts/laws-inventory.py` from `Graded/*.lean`. Do "
        "not hand-edit — see `docs/design.md#laws-inventory`.",
        "",
        "| theorem | module | properties | C++ law |",
        "|---|---|---|---|",
    ]
    for row in rows:
        props = ", ".join(row["properties"]) if row["properties"] else "—"
        theorem = row["theorem"].replace("|", "\\|")
        cpp = row["cpp"].replace("|", "\\|")
        md_lines.append(f"| `{theorem}` | `{row['module']}` | {props} | {cpp} |")
    md_lines.append("")
    (docs_dir / "laws.md").write_text("\n".join(md_lines))

    write_probe_harness(docs_dir, rows)


def write_probe_harness(docs_dir: Path, rows):
    """The input to the C++ side: one probe per row that has a C++ law,
    against `beman::transpose` names as given in
    `docs/design.md#cpp-counterpart` (`expected<T, error_set<Es...>>`,
    `and_then`, `transform_error`, `transpose`; `apply`/`transform` for the
    applicative/functor operations `docs/design.md#cpp-counterpart` and
    `#applicative` describe but do not themselves name). Nothing here runs
    C++ — this is the equation list a probe harness built from `std`
    types checks by example."""
    lines = [
        "# Probe harness",
        "",
        "Generated by `scripts/laws-inventory.py` from `docs/laws.json`. Do "
        "not hand-edit — see `docs/design.md#laws-inventory`.",
        "",
        "One probe per tabulated law that has a C++ equation "
        "(`docs/laws.md`'s non-`—` rows). Each is checked by example with "
        "`std` types (`std::expected`-shaped probes, per "
        "`docs/design.md#cpp-counterpart`'s decision that the CRTP "
        "machinery itself does no law-checking); equality is `==` on the "
        "carrier after conversion. Nothing here runs C++.",
        "",
    ]
    for row in rows:
        if row["cpp"] == "—":
            continue
        lines.append(f"## `{row['theorem']}` ({row['module']})")
        lines.append("")
        lines.append(f"    {row['cpp']}")
        lines.append("")
        lines.append(
            "check by example with std types; equality is `==` on the "
            "carrier after conversion."
        )
        lines.append("")
    (docs_dir / "probe-harness.md").write_text("\n".join(lines))


if __name__ == "__main__":
    main()
