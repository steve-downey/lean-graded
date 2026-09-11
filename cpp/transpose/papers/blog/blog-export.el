;;; blog-export.el --- Shared Org->HTML export config for the transpose blog  -*- lexical-binding: t; -*-

;;; Commentary:
;;
;; Loaded by the `papers/blog' Makefile on top of the repo `.emacs.d/init.el'
;; (which supplies org, htmlize, citeproc, and org-transclusion).  Its only job
;; is to make a standalone HTML export succeed for posts that are normally
;; published to sdowney.org through org2blog.
;;
;; `{{{TEASER_END}}}' is org2blog's "read more" fold marker.  The publishing
;; path defines it; a bare `org-export-to-file' does not, and Org aborts on the
;; undefined macro.  We define it here as the empty string (the teaser fold is
;; meaningless in a single self-contained page).  `modification-time' is a
;; built-in Org macro and needs no help.

;;; Code:

(require 'org)

;; The "with running code" posts capture program output through sh src blocks
;; (:results output :exports results) that run example binaries during export.
;; The repo init.el loads ob-shell inside a use-package form gated on flycheck,
;; which never triggers in batch, so load it here and let the blocks run
;; unprompted.
(require 'ob-shell)
(setq org-confirm-babel-evaluate nil)

;; Also normally set by the flycheck-gated use-package form: without it the
;; exporter re-indents transcluded src blocks and mangles continuation lines.
(setq org-src-preserve-indentation t)
;; And keep that re-indentation from introducing tabs into all-space sources.
(setq-default indent-tabs-mode nil)

(setq org-export-global-macros
      (append '(("TEASER_END" . ""))
              (and (boundp 'org-export-global-macros) org-export-global-macros)))

;; Citations use the built-in `basic' processor: no #+cite_export / CSL setup is
;; present in the posts, and it renders [cite:@key] + #+print_bibliography: from
;; the local references.bib without pulling in a style file.
(with-eval-after-load 'oc
  (setq org-cite-export-processors '((t basic))))

;; The `orgit-file:' links (both the `#+transclude:' ones and the inline source
;; permalinks) are handled by `.emacs.d/lisp/orgit-file-transclusion.el', which
;; the repo init.el requires.  It resolves REPO::REV::PATH::UUID against a
;; pinned git revision and registers the export handler that turns an inline
;; link into a forge permalink at that revision.  Nothing is needed here.

(provide 'blog-export)
;;; blog-export.el ends here
