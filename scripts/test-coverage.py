#!/usr/bin/env python3
"""Mechanical test-coverage check for the Lean model of graded Transpose.

A companion pass over `laws-inventory.py`'s existing parse, not a second
parser: it reuses that script's `theorem_chunks` carving and its generated
`docs/laws.json` rows, and adds one question — *is this declaration
exercised by a test?*

`docs/RULES.md` has always required that `Tests/<Module>.lean` instantiate
every theorem of its step and compute at least one `#guard`. That was
enforced by review, and review missed things: a name-reference audit at
[truth-in-labelling] found dozens of theorems whose names appear nowhere
in `Tests/` or `Examples/`. This script is that audit, run every build.

**Why classes rather than one rule.** Requiring a per-theorem `example`
for everything would, on the tree this was written against, need dozens of
hand-written exemptions on day one, almost all of them `rfl` reduction
lemmas (`foldGrade_nil`, `cast_ok`, `apK_err_left` and their kin). Those
are not untested; they are the equations every `#guard` in the repository
computes *through*. Writing prose justifications for them produces a file
nobody reads, and teaches the next contributor that the exemption file is
where theorems go to be ignored. So each declaration is classified, and
each class has one rule:

| class | detection | rule |
|---|---|---|
| counterexample | statement contains `¬` or `≠` | a test names it |
| reduction | proof is `rfl` | its module's test file has a `#guard`/`decide` that computes |
| law | everything else | a test names it |

Classification is by priority in that order: a `¬` proved by `rfl` is a
counterexample, not a reduction, because what it refutes is the point.

**"A test names it" is checked against comment-stripped source.** A
theorem mentioned only in a test file's prose is not covered, and neither
is one reachable only through an import. That is the specific failure mode
this script exists to prevent, so it is worth saying twice.

**Exemptions** live in `scripts/coverage-exemptions.json`, a JSON object
mapping a theorem's name (as captured, dot-qualification included) to the
reason it is exempt, in prose a reviewer signed off. It was introduced
empty and should stay close to it: an entry is a finding about the
theorem, not a way to quiet the check. `docs/RULES.md` carries the fixture
requirements that a passing check cannot enforce.
"""

import importlib.util
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GRADED_DIR = ROOT / "Graded"
TEST_DIRS = (ROOT / "Tests", ROOT / "Examples")
EXEMPTIONS_PATH = Path(__file__).resolve().parent / "coverage-exemptions.json"

# Reuse the inventory's own parse rather than re-deriving it.
_spec = importlib.util.spec_from_file_location(
    "laws_inventory", Path(__file__).resolve().parent / "laws-inventory.py"
)
laws_inventory = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(laws_inventory)

NAMESPACE_RE = re.compile(r"^(namespace|end)\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.MULTILINE)
BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT_RE = re.compile(r"--[^\n]*")
COMPUTES_RE = re.compile(r"#guard\b|\bdecide\b")


def strip_comments(text: str) -> str:
    """Remove Lean block and line comments. Coverage is a claim about
    code, so prose mentioning a theorem must not count as exercising it."""
    return LINE_COMMENT_RE.sub("", BLOCK_COMMENT_RE.sub("", text))


def qualified_names(path: Path) -> dict[str, str]:
    """Map each theorem's captured name to its fully-qualified name, by
    tracking the `namespace`/`end` stack at the point of declaration.
    `end` closing a `section` is ignored, since sections do not qualify."""
    text = path.read_text()
    opens = []  # (offset, kind, name)
    for m in NAMESPACE_RE.finditer(text):
        opens.append((m.start(), m.group(1), m.group(2)))
    out = {}
    for m in laws_inventory.THEOREM_RE.finditer(text):
        stack = []
        for off, kind, name in opens:
            if off > m.start():
                break
            if kind == "namespace":
                stack.append(name)
            elif stack and stack[-1] == name:
                stack.pop()
        out[m.group(1)] = ".".join(stack + [m.group(1)])
    return out


def remove_balanced(text: str) -> str:
    """Drop every balanced `(...)`, `{...}` and `[...]` group. Binders are
    always bracketed in Lean, so what survives is the top-level shape of a
    signature: enough to tell a conclusion from a hypothesis, which is the
    only question `classify` asks of it. Without this, a reduction lemma
    carrying a non-emptiness hypothesis (`hne : es ≠ []`) reads as a
    refutation."""
    out, depth = [], 0
    for ch in text:
        if ch in "({[":
            depth += 1
        elif ch in ")}]":
            depth = max(0, depth - 1)
        elif depth == 0:
            out.append(ch)
    return "".join(out)


def classify(chunk: str) -> str:
    """counterexample / reduction / law, in that priority. A `¬` proved by
    `rfl` is a counterexample: what it refutes is the point."""
    statement, _, proof = chunk.partition(":=")
    skeleton = remove_balanced(statement)
    if "¬" in skeleton or "≠" in skeleton:
        return "counterexample"
    proof = proof.strip()
    if proof == "rfl" or proof == "by rfl":
        return "reduction"
    return "law"


def load_test_text() -> str:
    parts = []
    for d in TEST_DIRS:
        for path in sorted(d.rglob("*.lean")):
            parts.append(strip_comments(path.read_text()))
    return "\n".join(parts)


def module_computes(module: str) -> bool:
    """Does this module's own test file contain something that reduces?

    Tries the exact mirror first (`Graded/Foo.lean` -> `Tests/Foo.lean`),
    then the parent directory's name. [module-split] put six modules under
    `Graded/Sufficient/`, whose tests all live in the one
    `Tests/Sufficient.lean` rather than in a mirrored tree; without the
    fallback every reduction lemma in them reads as uncovered."""
    rel = Path(module).relative_to("Graded")
    candidates = [ROOT / "Tests" / rel, ROOT / "Tests" / (rel.parent.name + ".lean")]
    for test_path in candidates:
        if test_path.exists() and COMPUTES_RE.search(strip_comments(test_path.read_text())):
            return True
    return False


def named_in(name: str, text: str) -> bool:
    """The name exactly as declared, dot-qualification included. An
    earlier version also accepted the final segment of a dotted name, on
    the theory that a test with `open Graded.Comp` would spell
    `Comp.ap_ok_ok` bare — and that promptly counted `Comp.ap_ok_ok` as
    covered by an example applying `Graded.ap_ok_ok`, a different theorem
    with the same last segment. Over-crediting is the one failure this
    script exists to prevent, so the fallback is gone: write the name the
    way it is declared, or take an exemption.

    The residual weakness is the one `laws-inventory.py` documents for its
    own allow-list: two theorems declared under the same bare name in
    different namespaces (`Graded.ap_ok_ok` and `Graded.Accum.ap_ok_ok`)
    are indistinguishable here, and a mention of the bare name credits
    both. Rows stay apart by module; this check does not."""
    return bool(laws_inventory._mention_re(name).search(text))


def main() -> None:
    exemptions = json.loads(EXEMPTIONS_PATH.read_text())
    test_text = load_test_text()

    chunks = {}
    quals = {}
    for path in sorted(GRADED_DIR.rglob("*.lean")):
        module = f"Graded/{path.relative_to(GRADED_DIR)}"
        quals[module] = qualified_names(path)
        for name, chunk in laws_inventory.theorem_chunks(path):
            chunks[(module, name)] = chunk

    uncovered = []
    counts = {"counterexample": 0, "reduction": 0, "law": 0}
    for (module, name), chunk in sorted(chunks.items()):
        cls = classify(chunk)
        counts[cls] += 1
        if name in exemptions:
            continue
        covered = module_computes(module) if cls == "reduction" else named_in(name, test_text)
        if not covered:
            uncovered.append((module, name, cls))

    if "--report" in sys.argv[1:]:
        for (module, name), chunk in sorted(chunks.items()):
            print(f"{classify(chunk):15s} {module}: {name}")
        return

    if "--qualified" in sys.argv[1:]:
        # Fully-qualified names of the `law`-class declarations, for
        # `scripts/axioms-check.py` to feed to `#print axioms`. Namespaces
        # come from tracking the `namespace`/`end` stack at the point of
        # declaration, not from guessing, because a bare `toGraded_grade'`
        # inside `namespace Accum` and a dotted `Comp.ap_pure_id` inside
        # `namespace Graded` are qualified differently and neither is
        # recoverable from the captured name alone.
        for (module, name), chunk in sorted(chunks.items()):
            if classify(chunk) == "law" and name not in exemptions:
                print(quals[module][name])
        return

    if uncovered:
        sys.stderr.write(
            "test-coverage: the following declarations are not exercised by "
            "any test — add an `example` that applies the theorem (or a "
            "computing `#guard` in the module's test file, for a "
            "reduction), or a reviewed entry in "
            "scripts/coverage-exemptions.json:\n"
        )
        for module, name, cls in uncovered:
            sys.stderr.write(f"  [{cls}] {module}: {name}\n")
        sys.stderr.write(f"({len(uncovered)} uncovered)\n")
        sys.exit(1)

    total = sum(counts.values())
    print(
        f"test-coverage: {total} declarations covered "
        f"({counts['law']} law, {counts['reduction']} reduction, "
        f"{counts['counterexample']} counterexample), "
        f"{len(exemptions)} exempt."
    )


if __name__ == "__main__":
    main()
