.PHONY: verify nosorry letters laws test-coverage axioms all cpp-probes blog-md
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
# Not part of `all`: needs a C++23 toolchain, cmake and ninja, and fetches
# Catch2 through transpose's own lockfile. Builds only the probe harness
# binary, out of tree, and runs it. See docs/RULES.md#c-obligations.
CPP_PROBES_BUILD ?= .build/cpp-probes
cpp-probes:
	@mkdir -p $(CPP_PROBES_BUILD)
	@cmake -S cpp/transpose -B $(CPP_PROBES_BUILD) -G Ninja \
	  -DCMAKE_BUILD_TYPE=Debug \
	  -DCMAKE_PROJECT_TOP_LEVEL_INCLUDES=./infra/cmake/use-fetch-content.cmake \
	  -DBEMAN_TRANSPOSE_BUILD_EXAMPLES=OFF > $(CPP_PROBES_BUILD)/configure.log 2>&1 \
	  || { tail -n 20 $(CPP_PROBES_BUILD)/configure.log; exit 1; }
	@cmake --build $(CPP_PROBES_BUILD) --target beman.transpose.tests.probe_harness \
	  > $(CPP_PROBES_BUILD)/build.log 2>&1 \
	  || { tail -n 40 $(CPP_PROBES_BUILD)/build.log; exit 1; }
	@$(CPP_PROBES_BUILD)/tests/beman/transpose/beman.transpose.tests.probe_harness

blog-md:
	@$(MAKE) -C blog/letters blog-md
