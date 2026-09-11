;;; init.el --- Repository-local Org export setup  -*- lexical-binding: t; -*-

;; Adapted from transpose/.emacs.d/init.el.  Keep the exporter and its
;; packages inside the repository so `make blog-md' is reproducible and does
;; not depend on a developer's personal Emacs configuration.

(setq custom-file (locate-user-emacs-file "custom.el"))

(require 'package)
(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/") t)
(setq package-user-dir
      (locate-user-emacs-file (concat "elpa-" emacs-version)))
(package-initialize)

(unless (and (package-installed-p 'ox-gfm)
             (package-installed-p 'org-transclusion))
  (package-refresh-contents)
  (dolist (pkg '(ox-gfm org-transclusion))
    (unless (package-installed-p pkg)
      (package-install pkg))))

(require 'org)
(require 'ox-gfm)
(require 'org-transclusion)

;; Preserve Lean and C++ spelling and indentation in prose and source blocks.
(setq org-use-sub-superscripts '{})
(setq org-export-with-sub-superscripts '{})
(setq org-src-preserve-indentation t)
(setq-default indent-tabs-mode nil)

(add-to-list 'load-path
             (expand-file-name
              "lisp" (or (and load-file-name
                              (file-name-directory load-file-name))
                         user-emacs-directory)))
(require 'orgit-file-transclusion)

;;; init.el ends here
