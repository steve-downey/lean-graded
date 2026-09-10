.PHONY: verify nosorry letters laws test-coverage axioms all
all: verify nosorry letters laws test-coverage axioms
verify:
	lake build > build.log 2>&1 || { tail -n 20 build.log; exit 1; }
	@tail -n 20 build.log
nosorry:
	@files=$$(find . -name '*.lean' -not -path './.lake/*'); \
	test -n "$$files" || { echo "nosorry: no .lean files found"; exit 1; }; \
	for pat in '\bsorry\b|\badmit\b|native_decide' '^[[:space:]]*axiom\b'; do \
	  grep -nE "$$pat" $$files; rc=$$?; \
	  case $$rc in \
	    0) echo "nosorry: FAILED (matches above)"; exit 1 ;; \
	    1) ;; \
	    *) echo "nosorry: grep error $$rc"; exit $$rc ;; \
	  esac; \
	done; \
	echo "nosorry: clean"
letters:
	@scripts/check-letters.sh
laws:
	@python3 scripts/laws-inventory.py
	@git diff --exit-code -- docs/laws.md docs/laws.json || \
	  { echo "laws: docs/laws.md/docs/laws.json are stale — commit the regenerated output"; exit 1; }
test-coverage:
	@python3 scripts/test-coverage.py
axioms:
	@python3 scripts/axioms-check.py
