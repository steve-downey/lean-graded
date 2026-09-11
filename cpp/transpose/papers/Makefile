# papers/Makefile                                                 -*-makefile-*-
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#
# Papers are built with MPark.WG21, vendored as a squashed subtree under
# wg21/. Its flat layout expects the papers to sit beside the framework, which
# is what this directory is.
#
#   make D3200R0.html   # generated/D3200R0.html from D3200R0.md
#   make D3200R0.pdf
#   make                # every paper, in the default format
#
# defaults.yaml adds the wording transclusion filter; see
# ../docs/wording-pipeline.md.

include wg21/flat.mk

# The generated wording fragments are spliced in by filters/transclude.py, so a
# paper must rebuild when they change. The fragments themselves must NOT be
# prerequisites: base.mk passes every `%.md` prerequisite to pandoc as a
# further input file. Depend on the stamp `make wording` writes instead.
$(OUTDIR)/D3200R0.html $(OUTDIR)/D3200R0.latex $(OUTDIR)/D3200R0.pdf: \
    wording/.stamp filters/transclude.py
