#!/usr/bin/env bash
# scripts/gen-wording.sh                                              -*-sh-*-
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#
# Generates the P3200 wording fragments from the marked-up headers.
#
# Each header is rendered on its own -- beman.specgen reads only the main
# file's declaration/comment interleave -- so each contributes its own
# synopsis subclause. `--root` names that synopsis, which is what keeps the
# root fragments distinct in the shared output directory.
#
# `--split` never deletes files left by an earlier run, so each header's
# ordered manifest is written beside the fragments and is the record the
# paper's include order is reconciled against.
#
# Usage: scripts/gen-wording.sh [output-directory]

set -o nounset
set -o errexit
set -o pipefail
IFS=$'\n\t'

readonly REPO_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

SPECGEN="${SPECGEN:-specgen}"
OUT_DIR="${1:-$REPO_ROOT/papers/wording}"

# Headers to generate wording from, paired with the stable-name stem their
# subclauses live under. Add a header here once it carries specgen markup and
# validates clean.
readonly HEADERS=(
    "apply.hpp:transpose.applicative"
    "traverse.hpp:transpose.traversable"
    "transpose.hpp:transpose.alg"
    "sequence.hpp:transpose.range"
    "array.hpp:transpose.array"
    "grade.hpp:transpose.grade"
    "error_set.hpp:transpose.errset"
    "expected.hpp:transpose.expected"
)

# The specgen-supported front end is Clang 22 against a C++26 standard
# library. Flags are passed explicitly rather than through a compilation
# database, because headers are not translation units in one.
readonly CLANG_ARGS=(
    -std=c++2c
    "-I$REPO_ROOT/include"
)

if ! command -v "$SPECGEN" > /dev/null 2>&1; then
    echo "gen-wording: error: '$SPECGEN' not found; set SPECGEN to its path" >&2
    exit 1
fi

mkdir -p "$OUT_DIR"

for entry in "${HEADERS[@]}"; do
    header="${entry%%:*}"
    stem="${entry#*:}"

    echo "gen-wording: $header -> $stem.*"
    # Run from the output directory with a relative `--split` so the manifest
    # records `<stable name>.md` rather than a path particular to this machine.
    (
        cd "$OUT_DIR"
        "$SPECGEN" generate "$REPO_ROOT/include/beman/transpose/$header" \
            --backend mpark \
            --validate \
            --paper \
            --root "$stem.syn" \
            --split . \
            --no-compile-commands \
            -- "${CLANG_ARGS[@]}" \
            > "$stem.manifest"
    )
done

# A stamp the paper build can depend on. The fragments themselves must not
# become prerequisites of the paper: the vendored MPark.WG21 Makefile passes
# every `%.md` prerequisite to pandoc as an input file.
date -u +%Y-%m-%dT%H:%M:%SZ > "$OUT_DIR/.stamp"

echo "gen-wording: wrote $OUT_DIR"
