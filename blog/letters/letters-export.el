;;; letters-export.el --- Org export settings for the Lean letters -*- lexical-binding: t; -*-

;; Kept separate from init.el, following transpose/papers/blog/blog-export.el,
;; so series-specific export behavior can evolve without changing package
;; bootstrap code.

(require 'org)
(require 'ox-gfm)

(setq org-src-preserve-indentation t)
(setq-default indent-tabs-mode nil)

;; GitHub already provides useful heading anchors.  Org's generated table of
;; contents instead exposes unstable `org...' anchors and adds little to these
;; short letters.
(setq org-export-with-toc nil)

;; ox-gfm's body template omits the document title.  That is useful for the
;; transpose posts when they are embedded in a blog, but these files are read
;; directly on GitHub and need their title as an H1.
(defun letters-export-gfm-inner-template (original contents info)
  "Add the Org document title around ORIGINAL's GFM body."
  (let ((body (funcall original contents info)))
    (if (plist-get info :with-title)
        (concat "# " (org-export-data (plist-get info :title) info)
                "\n\n" body)
      body)))

(advice-add 'org-gfm-inner-template :around
            #'letters-export-gfm-inner-template)

(provide 'letters-export)
;;; letters-export.el ends here
