(provide cv-help)

(@doc "\
  Helpers used to build `@doc` docstrings for the `cryptovampire/*` libraries.

  `cv-help` renders a small markdown block: a bold `title`, a `Usage:` line
  with the snippet in backticks, then the free-form body `paras`.  It is meant
  to be called as the *documentation* expression of the `@doc` macro:

  ```scheme
  (@doc (cv-help \"my-fn\" \"(my-fn a b)\" \"Adds a and b.\") (define (my-fn a b) (+ a b)))
  ```

  **TITLE**  -- function name (string)
  **USAGE**  -- a scheme call snippet (string)
  **PARAS**  -- body paragraphs (strings); use ```scheme fenced blocks for examples

  This also help defeat the overzealous auto-formating.
  "
  (define (cv-help title usage . paras)
    (string-join
      (append (list (string-append "**`" title "`**") ""
          (string-append "**Usage:** `" usage "`") "")
        paras)
      "\n")))