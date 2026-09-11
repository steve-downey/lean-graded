#!/usr/bin/env python3

# papers/filters/bibliography-header.py
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#
# Works around an upstream MPark.WG21 defect.
#
# `wg21.py`'s `header` action does
#
#     if elem.identifier == 'bibliography':
#         elem.classes.remove('unnumbered')
#
# unconditionally. Pandoc 3.9's citeproc does not put `unnumbered` on the
# generated references header, so the removal raises
#
#     ValueError: list.remove(x): x not in list
#
# and the filter aborts. Any paper with a citation fails; a twelve-line paper
# with one `[@Pnnnn]` is enough to reproduce it.
#
# This filter runs between citeproc and wg21.py -- see ../defaults.yaml -- and
# restores the class that wg21.py expects to remove. The end state is the one
# wg21.py intends: a numbered references header. It is a shim, not a
# preference, and it should be deleted once upstream guards that removal.

import panflute as pf


def action(element, doc):
    if not isinstance(element, pf.Header):
        return None
    if element.identifier == "bibliography" and "unnumbered" not in element.classes:
        element.classes.append("unnumbered")
    return None


def main(doc=None):
    return pf.run_filter(action, doc=doc)


if __name__ == "__main__":
    main()
