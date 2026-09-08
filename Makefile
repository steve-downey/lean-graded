.PHONY: verify nosorry letters all
all: verify nosorry letters
verify:
	lake build 2>&1 | tee build.log | tail -n 20
	@grep -q "error" build.log && exit 1 || true
nosorry:
	@! grep -rnE "\bsorry\b|\badmit\b|native_decide" Graded Tests Examples --include=*.lean
	@! grep -rnE "^\s*axiom\b" Graded Tests Examples --include=*.lean
letters:
	@scripts/check-letters.sh
