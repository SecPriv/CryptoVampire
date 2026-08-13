(provide cv-help make-doc-table doc-add!)

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

;; ---------------------------------------------------------------------------
;; Per-library documentation tables.
;;
;; The `help` doc table only stores closures, so macros, plain sorts and
;; re-exports cannot carry a `@doc`.  Such documentation lives in a small
;; registry next to the definition, in the library that owns it.
;;
;; `make-doc-table` returns a fresh, empty documentation table and `doc-add!`
;; records one entry.  Both are *pure* (`doc-add!` returns the new table), so
;; they are safe to share across modules.
;;
;; Steel modules are evaluated once and their instances are *shared*, but
;; `require`/`provide` copy *values* into the requirer: an imported top-level
;; binding is a snapshot of that module's cell taken at import time and does
;; not track later `set!`s.  Live module state is only observable *through a
;; closure* defined in that module -- calling it reads/writes the module's own
;; cell at call time (this is why `get-function`/`insert-function` around
;; `function.scm`'s `functions-map` work across modules, and why the `@doc`
;; `help` tables, which live in shared native/closure state, work everywhere).
;;
;; A centrally shared `syntax-docs`-style registry would therefore show up as
;; an imported value snapshot that goes stale once the registering modules run:
;; each owning library thus builds its own table with a local `register-*!`
;; helper and exports the *finished* table -- reading back a complete value
;; needs no live sharing at all.  This is the same shape as
;; `cryptovampire/builtin-functions`' `builtin-doc`, which `mk_scheme_lib`
;; builds up entirely inside the module body it emits (intra-module `set!`,
;; then export the completed value).
;; `crates/indistinguishability/scheme/docgen.scm` collects them to render
;; `docs/scheme-api.md`.
;; ---------------------------------------------------------------------------

(define (make-doc-table) (hash))
(define (doc-add! table name . doc)
  (hash-insert table name (string-join doc "\n")))
