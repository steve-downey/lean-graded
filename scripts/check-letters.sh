#!/usr/bin/env bash
# For every "- [x] N. [slug]" line in tmp/plan/checklist.md, require
# blog/letters/<slug>.org to exist and contain the four required headings.
# baseline-capture is exempt from the "What the checker refused" heading.
# blog-series-edit is exempt entirely (its output is the index, not a letter).
set -u

checklist="tmp/plan/checklist.md"
letters_dir="blog/letters"

fail() {
	echo "check-letters: $1" >&2
	exit 1
}

[ -f "$checklist" ] || fail "missing $checklist"

while IFS= read -r line; do
	slug=$(printf '%s\n' "$line" | sed -nE 's/^- \[x\] [0-9]+\. \[([a-z0-9-]+)\].*/\1/p')
	[ -n "$slug" ] || continue

	if [ "$slug" = "blog-series-edit" ]; then
		continue
	fi

	letter="${letters_dir}/${slug}.org"
	[ -f "$letter" ] || fail "missing letter: $letter"

	for heading in \
		"* What I set out to do" \
		"* What changed" \
		"* Back in C++"; do
		grep -qF "$heading" "$letter" || fail "$letter missing heading: $heading"
	done

	if [ "$slug" != "baseline-capture" ]; then
		grep -qF "* What the checker refused" "$letter" \
			|| fail "$letter missing heading: * What the checker refused"
	fi
done < "$checklist"

exit 0
