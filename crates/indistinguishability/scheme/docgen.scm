;; docgen.scm
;;
;; Generates `docs/scheme-api.md`: a markdown reference of the `cryptovampire/*`
;; scheme libraries and of the Rust-exported builtin functions.
;;
;;   * functions  -- extracted from the `help` doc tables (Rust doc comments via
;;                   `#%native-fn-ptr-doc->string`, and the steel `@doc` table via
;;                   `#%function-ptr-table-get`);
;;   * macros / sorts / builtin functions -- read from the *documentation tables*
;;                   each library owns and exports:
;;                      function-doc formula-doc protocol-doc solver-doc
;;                      signature-doc sort-doc builtin-doc
;;                   (see `cryptovampire/doc` and each library for the mechanism;
;;                   `builtin-doc` holds the docs the builtin wrappers inherited
;;                   from their unwrapped Rust functions).
;;
;; Note: helpers here deliberately avoid dotted-rest closures that are called
;; from later definitions (a steel alpha-renaming edge case): everything builds
;; plain strings which are written with the fixed-arity `doc-put`.
;;
;; Regenerate from the repository root with:
;;   cargo run --release -- crates/indistinguishability/scheme/docgen.scm

(require "cryptovampire/stdlib")
(require "cryptovampire/function")
(require "cryptovampire/formula")
(require "cryptovampire/protocol")
(require "cryptovampire/solver")
(require "cryptovampire/cryptography")
(require "cryptovampire/signature")
(require "cryptovampire/sort")
(require "cryptovampire/type")
(require "cryptovampire/builtin-functions")

;; ---------------------------------------------------------------------------
;; doc extraction
;; ---------------------------------------------------------------------------

;; Raw markdown doc string for a function value: Rust doc comment first, then
;; the steel `@doc` table.  Returns #f when undocumented.
(define (raw-doc f)
  (or (#%native-fn-ptr-doc->string f)
      (#%function-ptr-table-get #%function-ptr-table f)))

;; cv-help docs start with the bold title line (`` **`name`** ``); drop it since
;; the section headings already carry the name.
(define (strip-title-line s)
  (let loop ((i 0) (n (string-length s)))
    (cond
      [(>= i n) s]
      [(char=? (string-ref s i) #\newline)
       (if (= i (- n 1)) "" (substring s (+ i 1) n))]
      [else (loop (+ i 1) n)])))

;; ---------------------------------------------------------------------------
;; ordered lists of (name . value) per module
;; ---------------------------------------------------------------------------

(define function-fns
  (list
    (cons 'nonce? nonce?)
    (cons 'get-function get-function)
    (cons 'get-input-sorts get-input-sorts)
    (cons 'get-output-sort get-output-sort)
    (cons 'wrap-nonce wrap-nonce)
    (cons 'unwrap-nonce unwrap-nonce)
    (cons 'lift-function lift-function)
    (cons 'register-function register-function)
    (cons 'declare-function declare-function)
    (cons 'mk-function mk-function)
    (cons 'arity arity)
    (cons 'mk-alias-rw mk-alias-rw)
    (cons 'convert-to-formula convert-to-formula)))

(define formula-fns
  (list
    (cons 'mexists mexists)
    (cons 'mforall mforall)
    (cons 'mfindst mfindst)
    (cons 'cand cand)
    (cons 'cor cor)
    (cons 'ctuple ctuple)
    (cons 'subst subst)))

(define protocol-fns
  (list
    (cons 'declare-step declare-step)
    (cons 'declare-same-step declare-same-step)
    (cons 'declare-memory-cell declare-memory-cell)
    (cons 'empty-assignements empty-assignements)))

(define solver-fns
  (list
    (cons 'add-golgge-rule add-golgge-rule)
    (cons 'add-smt-axiom add-smt-axiom)
    (cons 'add-rewrite add-rewrite)
    (cons 'run run)
    (cons 'mk-problem mk-problem)
    (cons 'declare-protocol declare-protocol)))

(define cryptography-fns
  (list
    (cons 'declare-cryptography declare-cryptography)
    (cons 'register-fresh-nonce register-fresh-nonce)
    (cons 'initialize-as initialize-as)
    (cons 'initialize-as-prf initialize-as-prf)
    (cons 'initialize-as-ddh initialize-as-ddh)
    (cons 'initialize-as-aenc initialize-as-aenc)
    (cons 'initialize-as-senc initialize-as-senc)
    (cons 'initialize-as-xor initialize-as-xor)))

(define stdlib-fns
  (list (cons 'partial partial)))

;; ---------------------------------------------------------------------------
;; rendering
;; ---------------------------------------------------------------------------

(define doc-pt #f)
(define (doc-put s) (display s doc-pt))

;; Entries of a documentation table as a list of (name . doc), sorted by name.
(define (key-string k) (if (string? k) k (symbol->string k)))

(define (table-entries table)
  (map
    (lambda (p) (cons (car p) (hash-ref table (cdr p))))
    (sort
      (map (lambda (k) (cons (key-string k) k)) (hash-keys->list table))
      (lambda (a b) (string<? (car a) (car b))))))

(define (fns-section pairs)
  (apply string-append
    (map
      (lambda (p)
        (let ((name (car p)) (f (cdr p)))
          (let ((d (raw-doc f)))
            (if d
              (string-append "\n#### " (symbol->string name) "\n\n" (strip-title-line d) "\n")
              ""))))
      pairs)))

;; Render one documentation-table entry (macro / value / builtin) as markdown,
;; skipping entries without any documentation.
(define (entry-section heading entry)
  (if (string=? (cdr entry) "")
    ""
    (string-append
      "\n" heading " " (car entry) "\n\n" (cdr entry) "\n")))

(define (table-entries->section table heading)
  (apply string-append (map (lambda (e) (entry-section heading e)) (table-entries table))))

(define (module-section title fns table)
  (doc-put
    (string-append
      "\n## " title "\n"
      (if (null? fns)
        ""
        (string-append "\n### Functions\n" (fns-section fns)))
      (if (hash? table)
        (string-append "\n### Macros & values\n" (table-entries->section table "####"))
        ""))))

;; ---------------------------------------------------------------------------

(create-directory! "docs")

(call-with-output-file "docs/scheme-api.md"
  (lambda (port)
    (set! doc-pt port)
    (doc-put
      (string-append
        "# CryptoVampire Scheme API\n\n"
        "Reference of the `cryptovampire/*` scheme libraries and of the\n"
        "Rust-exported builtin functions.\n"
        "Generated from the `help` doc tables and the per-library documentation\n"
        "tables (see `cryptovampire/doc`).\n\n"
        "Regenerate with:\n\n"
        "```sh\n"
        "cargo run --release -- crates/indistinguishability/scheme/docgen.scm\n"
        "```\n"))
    (doc-put "\n## Sorts & types\n")
    (doc-put (table-entries->section sort-doc "###"))
    (module-section "cryptovampire/stdlib" stdlib-fns #f)
    (module-section "cryptovampire/function" function-fns function-doc)
    (module-section "cryptovampire/formula" formula-fns formula-doc)
    (module-section "cryptovampire/protocol" protocol-fns protocol-doc)
    (module-section "cryptovampire/solver" solver-fns solver-doc)
    (module-section "cryptovampire/cryptography" cryptography-fns #f)
    (module-section "cryptovampire/signature" '() signature-doc)
    (module-section "cryptovampire/builtin-functions" '() builtin-doc)))

(displayln "wrote docs/scheme-api.md")
