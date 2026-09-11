# Render the Lean-model letter series as GitHub-Flavored Markdown.
# Adapted from transpose/papers/blog/Makefile.
#
#   make blog-md    # convert all letters to GFM
#   make clean      # remove generated Markdown
#
# The first run installs ox-gfm into the repository-local .emacs.d package
# directory and therefore needs network access once.

EMACS     ?= emacs
ROOT      := $(shell git rev-parse --show-toplevel)
EMACSDIR  := $(ROOT)/.emacs.d
EXPORT_EL := $(CURDIR)/letters-export.el
ADAPTER_EL := $(EMACSDIR)/lisp/orgit-file-transclusion.el

ORGFILES  := $(wildcard *.org)
MD        := $(ORGFILES:.org=.md)

.PHONY: all blog-md clean

all: blog-md

blog-md: $(MD)

%.md: %.org $(EXPORT_EL) $(EMACSDIR)/init.el $(ADAPTER_EL)
	$(EMACS) --init-directory=$(EMACSDIR)/ \
	  --batch --load $(EMACSDIR)/init.el \
	  --load $(EXPORT_EL) \
	  --visit $< \
	  --eval "(org-transclusion-mode t)" \
	  --eval "(org-export-to-file 'gfm \"$(abspath $@)\")"

clean:
	-rm -f $(MD)
