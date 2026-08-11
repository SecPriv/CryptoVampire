(provide partial cv-help)

;; ---------------------------------------------------------------------------
;; Helpers used to build `@doc` docstrings for the `cryptovampire/*` libraries.
;;
;; `cv-help` renders a small markdown block: a bold `title`, a `Usage:` line
;; with the snippet in backticks, then the free-form body `paras`.  It is meant
;; to be called as the *documentation* expression of the `@doc` macro:
;;
;; ```scheme
;; (@doc (cv-help "my-fn" "(my-fn a b)" "Adds a and b.") (define (my-fn a b) (+ a b)))
;; ```
;;
;; TITLE  -- function name (string)
;; USAGE  -- a scheme call snippet (string)
;; PARAS  -- body paragraphs (strings); use ```scheme fenced blocks for examples
(define (cv-help title usage . paras)
  (string-join
    (append (list (string-append "**`" title "`**") ""
                  (string-append "**Usage:** `" usage "`") "")
            paras)
    "\n"))

(@doc (cv-help "partial" "(partial f . args)"
  "Returns a function that applies `f` to the given `args` followed by the arguments of the call."
  "*Example:*" "```scheme"
  "(define add1 (partial + 1))"
  "(add1 2) ;; => 3" "```")
 (define (partial f . args)
  (lambda rest-args
    (apply f (append args rest-args)))))
