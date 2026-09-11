;;; orgit-file-transclusion.el --- transclude source at a git rev -*- lexical-binding: t; -*-
;; SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

;; Adapted from transpose/.emacs.d/lisp/orgit-file-transclusion.el.
;;
;; Link form: [[orgit-file:REPO::REV::PATH::SELECTOR]]
;; REV is normally an annotated `blog/<letter-basename>' tag.  SELECTOR is an
;; Org file-link search selector; these letters use a line number within the
;; immutable pinned blob, followed by a relative :lines range.

(require 'org-transclusion)
(require 'subr-x)

(defgroup orgit-file-transclusion nil
  "Transclude source regions pinned to a git revision."
  :group 'org-transclusion)

(defcustom orgit-file-transclusion-cache-dir
  (expand-file-name "orgit-file-transclusion" temporary-file-directory)
  "Directory holding disposable blobs extracted from git."
  :type 'directory
  :group 'orgit-file-transclusion)

(defcustom orgit-file-transclusion-base-url
  "https://github.com/steve-downey/lean-graded/blob/"
  "Forge URL through `blob/', with a trailing slash."
  :type 'string
  :group 'orgit-file-transclusion)

(defun orgit-file-transclusion--parse (raw)
  "Split RAW into (REPO REV PATH SELECTOR); signal on another shape."
  (let ((parts (split-string raw "::")))
    (unless (= 4 (length parts))
      (error "orgit-file link needs REPO::REV::PATH::SELECTOR, got: %s" raw))
    parts))

(defun orgit-file-transclusion--rev-parse (repo rev)
  "Resolve REV to a full commit SHA in REPO."
  (with-temp-buffer
    (unless (zerop (call-process "git" nil t nil
                                 "-C" (expand-file-name repo)
                                 "rev-parse" (concat rev "^{commit}")))
      (error "orgit-file: cannot resolve rev %s in %s (fetch tags?): %s"
             rev repo (string-trim (buffer-string))))
    (string-trim (buffer-string))))

(defun orgit-file-transclusion--blob-file (repo rev path selector)
  "Materialize PATH at REV in REPO and return the cache filename.
When SELECTOR is a line number, make that pinned line the first line of the
materialized file.  `org-transclusion-add-src-lines' only honors textual
search markers, so this gives numeric historical pins the same relative
`:lines' behavior as transpose's UUID markers."
  (let* ((sha (orgit-file-transclusion--rev-parse repo rev))
         (numeric-selector (string-match-p "\\`[0-9]+\\'" selector))
         (cache-root (if numeric-selector
                         (expand-file-name (concat "line-" selector)
                                           (expand-file-name sha
                                                             orgit-file-transclusion-cache-dir))
                       (expand-file-name sha orgit-file-transclusion-cache-dir)))
         (cached (expand-file-name
                  path cache-root)))
    (unless (file-exists-p cached)
      (make-directory (file-name-directory cached) t)
      (let ((tmp (concat cached ".partial")))
        (with-temp-buffer
          (unless (zerop (call-process "git" nil t nil
                                       "-C" (expand-file-name repo)
                                       "show" (format "%s:%s" sha path)))
            (error "orgit-file: git show %s:%s failed in %s: %s"
                   rev path repo (string-trim (buffer-string))))
          (when numeric-selector
            (goto-char (point-min))
            (forward-line (1- (string-to-number selector)))
            (delete-region (point-min) (point)))
          (let ((coding-system-for-write 'no-conversion))
            (write-region (point-min) (point-max) tmp nil 'quiet)))
        (rename-file tmp cached t)))
    cached))

(defun orgit-file-transclusion-add (link _plist)
  "Resolve an `orgit-file' LINK into a file link on its pinned blob."
  (when (string= "orgit-file" (org-element-property :type link))
    (pcase-let* ((`(,repo ,rev ,path ,selector)
                  (orgit-file-transclusion--parse
                   (org-element-property :path link)))
                 (numeric-selector (string-match-p "\\`[0-9]+\\'" selector))
                 (blob (orgit-file-transclusion--blob-file repo rev path selector)))
      (org-element-put-property link :type "file")
      (org-element-put-property link :path blob)
      (org-element-put-property link :raw-link
                                (if numeric-selector
                                    (concat "file:" blob)
                                  (concat "file:" blob "::" selector)))
      (org-element-put-property link :search-option
                                (unless numeric-selector selector))))
  nil)

(add-hook 'org-transclusion-add-functions #'orgit-file-transclusion-add)

(org-link-set-parameters
 "orgit-file"
 :export
 (lambda (path desc backend)
   (pcase-let* ((`(,_repo ,rev ,filepath ,selector)
                 (orgit-file-transclusion--parse path))
                (line-anchor (and (string-match-p "\\`[0-9]+\\'" selector)
                                  (concat "#L" selector)))
                (url (concat orgit-file-transclusion-base-url rev "/"
                             filepath line-anchor)))
     (cond
      ((memq backend '(md gfm)) (format "[`%s`](%s)" (or desc filepath) url))
      ((eq backend 'html)
       (format "<a href=\"%s\"><code>%s</code></a>" url (or desc filepath)))
      (t url)))))

(provide 'orgit-file-transclusion)
;;; orgit-file-transclusion.el ends here
