#!/usr/bin/env python3
"""Assert that every `law`-class theorem rests on nothing but Lean's own
three axioms.

`make nosorry` is a text grep. It cannot see an axiom reached through a
dependency, and it cannot see a `sorry` in a declaration nothing
references. `#print axioms` sees exactly that: the transitive closure of
what a proof actually rests on. The two checks are complements, and this
repository keeps both — neither subsumes the other.

The expected closure is `{propext, Classical.choice, Quot.sound}`: the
three axioms of Lean's own logic, which Mathlib uses throughout. Anything
else — `sorryAx` above all, but also any project axiom someone adds later
— fails the check and names the theorem.

Two prior reviews (`tmp/plan/INTEGRATION-REVIEW.md`,
`tmp/plan/MIGRATION-REVIEW.md`) ran this by hand over 25 declarations and
each reported those three and nothing else. This runs it over every
`law`-class declaration, every build, so the sample stops being a sample.
"""

import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

# `#print axioms Foo` prints one of:
#   'Foo' depends on axioms: [propext, Classical.choice, Quot.sound]
#   'Foo' does not depend on any axioms
# The name group is greedy to the last quote on the line, not to the
# first: this codebase has declarations whose names *end* in an
# apostrophe (`Grade.le_refl'`, `Accum.toGraded_grade'`), and a
# non-greedy group silently truncates them into names that then look
# like missing output.
DEPENDS_RE = re.compile(r"'(.+)' depends on axioms: \[([^\]]*)\]")
NO_AXIOMS_RE = re.compile(r"'(.+)' does not depend on any axioms")


def law_names() -> list[str]:
    out = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "test-coverage.py"), "--qualified"],
        capture_output=True, text=True, cwd=ROOT,
    )
    if out.returncode != 0:
        sys.stderr.write(out.stderr)
        sys.exit("axioms: could not enumerate law-class declarations")
    return [line.strip() for line in out.stdout.splitlines() if line.strip()]


def main() -> None:
    names = law_names()
    if not names:
        sys.exit("axioms: no law-class declarations found — check the enumerator")

    src = "import Graded\n" + "".join(f"#print axioms {n}\n" for n in names)
    with tempfile.NamedTemporaryFile(
        "w", suffix=".lean", dir=ROOT, delete=False, encoding="utf-8"
    ) as fh:
        fh.write(src)
        probe = Path(fh.name)

    try:
        run = subprocess.run(
            ["lake", "env", "lean", str(probe)],
            capture_output=True, text=True, cwd=ROOT,
        )
    finally:
        probe.unlink(missing_ok=True)

    text = run.stdout + run.stderr
    seen, bad = set(), []
    for m in DEPENDS_RE.finditer(text):
        name, axioms = m.group(1), {a.strip() for a in m.group(2).split(",") if a.strip()}
        seen.add(name)
        extra = axioms - ALLOWED
        if extra:
            bad.append((name, sorted(extra)))
    for m in NO_AXIOMS_RE.finditer(text):
        seen.add(m.group(1))

    missing = [n for n in names if n not in seen]
    if bad or missing or run.returncode != 0:
        if bad:
            sys.stderr.write("axioms: declarations resting on more than Lean's own three:\n")
            for name, extra in bad:
                sys.stderr.write(f"  {name}: {', '.join(extra)}\n")
        if missing:
            sys.stderr.write(
                "axioms: no `#print axioms` output for the following — the name "
                "may not resolve, which is itself a defect in the enumerator:\n"
            )
            for name in missing[:20]:
                sys.stderr.write(f"  {name}\n")
            if len(missing) > 20:
                sys.stderr.write(f"  ... and {len(missing) - 20} more\n")
        if run.returncode != 0 and not (bad or missing):
            sys.stderr.write(text[-2000:])
        sys.exit(1)

    print(
        f"axioms: {len(seen)} law-class declarations, closure is a subset of "
        f"{{propext, Classical.choice, Quot.sound}}."
    )


if __name__ == "__main__":
    main()
