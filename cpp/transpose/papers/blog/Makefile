# papers/blog/Makefile --- render the transpose persuasive blog series
#
# Reuses the repo's Org toolchain (../../.emacs.d/init.el: org, htmlize,
# citeproc, org-transclusion, ox-gfm, and the orgit-file-transclusion adapter)
# plus blog-export.el for the org2blog TEASER_END macro.
#
# Posts transclude source with [[orgit-file:REPO::REV::PATH::UUID]] links
# pinned to an annotated blog/<post-basename> tag (see pins.md), so the code
# in a post is frozen at the revision its prose was written against. That is
# also why the .deps rules below extract nothing for these posts: a pinned
# transclusion cannot change when the worktree does, so the only dependency is
# the .org file itself. The sed stays for any future worktree-resolved
# [[file:...::...]] link, which would depend on the source and does need one.
#
#   make            # build all posts to HTML
#   make blog-md    # convert all posts to GFM markdown (blog style)
#   make test       # smoke test: render all posts to HTML
#   make examples   # build the gcc-16 example binaries the posts run
#   make clean      # remove generated HTML/MD and dep files
#
# First run installs the Emacs packages named in .emacs.d/init.el into
# .emacs.d/elpa-<version> (needs network once); the store is gitignored.
#
# The "with running code" posts (graded-gadgets, transpose-at-work,
# traverse-does-all-the-work) execute org-babel shell blocks during export
# that run binaries from $(ROOT)/.build/build-gcc-16-cxx26/examples/RelWithDebInfo.
# Run `make examples` (or `make -C $(ROOT) TOOLCHAIN=gcc-16-cxx26
# CONFIG=RelWithDebInfo compile`) before exporting them; gcc-16 is what
# provides <simd> for the SIMD output.

EMACS     ?= emacs
ROOT      := $(shell git rev-parse --show-toplevel)
EMACSDIR  := $(ROOT)/.emacs.d
EXPORT_EL := $(CURDIR)/blog-export.el

ORGFILES  := $(wildcard *.org)
HTML      := $(ORGFILES:.org=.html)
MD        := $(ORGFILES:.org=.md)

.PHONY: all blog-md test clean examples

all: $(HTML)

examples:
	$(MAKE) -C $(ROOT) TOOLCHAIN=gcc-16-cxx26 CONFIG=RelWithDebInfo compile

blog-md: $(MD)

test: $(HTML)

%.html : %.org $(EXPORT_EL)
	$(EMACS) --init-directory=$(EMACSDIR)/ \
	  --batch --load $(EMACSDIR)/init.el \
	  -f package-initialize \
	  --load $(EXPORT_EL) \
	  --eval "(setq enable-local-variables :all)" \
	  --visit $< \
	  --eval "(org-transclusion-mode t)" \
	  --eval "(org-export-to-file 'html \"$@\")"
	@echo "$@ : \\" > $@.deps
	@echo "  $<" \\ >> $@.deps
	@sed -n "s/^.*\[\[file:\(\S*\)::.*$$/\1/p" < $< | sort -u | xargs -r printf "  %s \\\\\n" >> $@.deps

%.md : %.org $(EXPORT_EL)
	$(EMACS) --init-directory=$(EMACSDIR)/ \
	  --batch --load $(EMACSDIR)/init.el \
	  -f package-initialize \
	  --load $(EXPORT_EL) \
	  --eval "(setq enable-local-variables :all)" \
	  --visit $< \
	  --eval "(org-transclusion-mode t)" \
	  --eval "(require 'ox-gfm)" \
	  --eval "(org-export-to-file 'gfm \"$(abspath $@)\")"
	@echo "$@ : \\" > $@.deps
	@echo "  $<" \\ >> $@.deps
	@sed -n "s/^.*\[\[file:\(\S*\)::.*$$/\1/p" < $< | sort -u | xargs -r printf "  %s \\\\\n" >> $@.deps

-include $(ORGFILES:%.org=%.html.deps)
-include $(ORGFILES:%.org=%.md.deps)

clean:
	-rm -f $(HTML) $(MD) $(ORGFILES:%.org=%.html.deps) $(ORGFILES:%.org=%.md.deps)
