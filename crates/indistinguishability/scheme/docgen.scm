;; docgen.scm
;;
;; Generates `docs/scheme-api.md`: a markdown reference of the `cryptovampire/*`
;; scheme libraries.
;;
;;   * functions  -- extracted from the `help` doc tables (Rust doc comments via
;;                   `#%native-fn-ptr-doc->string`, and the `@doc` table via
;;                   `#%function-ptr-table-get`);
;;   * macros / sorts -- read from the `syntax-docs` / `types-docs` registries in
;;                   `cryptovampire/doc` (macro and value docs cannot live in the
;;                   `help` table, see the README in scheme/libs).
;;
;; Note: helpers here deliberately avoid dotted-rest closures that are called
;; from later definitions (a steel alpha-renaming edge case): everything builds
;; plain strings which are written with the fixed-arity `doc-put`.
;;
;; Regenerate from the repository root with:
;;   cargo run --release -- crates/indistinguishability/scheme/docgen.scm

(require "cryptovampire/stdlib")
(require "cryptovampire/doc")
(require "cryptovampire/function")
(require "cryptovampire/formula")
(require "cryptovampire/protocol")
(require "cryptovampire/solver")
(require "cryptovampire/cryptography")
(require "cryptovampire/signature")
(require "cryptovampire/sort")
(require "cryptovampire/type")

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

;; ordered macro names per module (looked up in `syntax-docs`)
(define function-syntax '(define-function define-alias alias-rw))
(define formula-syntax '(exists forall findst))
(define protocol-syntax '(store-cell))
(define solver-syntax '(bind prolog add-constrain publish))
(define signature-syntax '(signature))

;; ordered sort/type names (looked up in `types-docs`)
(define type-names
  '(Nonce Bool Bitstring Message Time Protocol Step Index Any Condition step tuple))

;; ---------------------------------------------------------------------------
;; rendering
;; ---------------------------------------------------------------------------

(define doc-pt #f)
(define (doc-put s) (display s doc-pt))

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

(define (syntax-doc n)
  (if (hash-contains? syntax-docs n) (hash-ref syntax-docs n) #f))

(define (type-doc n)
  (if (hash-contains? types-docs n) (hash-ref types-docs n) #f))

(define (syntax-section names)
  (apply string-append
    (map
      (lambda (n)
        (let ((d (syntax-doc n)))
          (if d
            (string-append "\n#### " (symbol->string n) "\n\n" d "\n")
            "")))
      names)))

(define (types-section names)
  (apply string-append
    (map
      (lambda (n)
        (let ((d (type-doc n)))
          (if d
            (string-append "\n### " (symbol->string n) "\n\n" d "\n")
            "")))
      names)))

(define (module-section title fns syntax-names)
  (doc-put
    (string-append
      "\n## " title "\n"
      (if (null? fns)
        ""
        (string-append "\n### Functions\n" (fns-section fns)))
      (if (null? syntax-names)
        ""
        (string-append "\n### Syntax rules\n" (syntax-section syntax-names))))))

;; ---------------------------------------------------------------------------

(call-with-output-file "docs/scheme-api.md"
  (lambda (port)
    (set! doc-pt port)
    (doc-put
      (string-append
        "# CryptoVampire Scheme API\n\n"
        "Reference of the `cryptovampire/*` scheme libraries.\n"
        "Generated from the `help` doc tables and the `syntax-docs`/`types-docs`\n"
        "registries in `cryptovampire/doc`.\n\n"
        "Regenerate with:\n\n"
        "```sh\n"
        "cargo run --release -- crates/indistinguishability/scheme/docgen.scm\n"
        "```\n"))
    (doc-put "\n## Sorts & types\n")
    (doc-put (types-section type-names))
    (module-section "cryptovampire/stdlib" stdlib-fns '())
    (module-section "cryptovampire/function" function-fns function-syntax)
    (module-section "cryptovampire/formula" formula-fns formula-syntax)
    (module-section "cryptovampire/protocol" protocol-fns protocol-syntax)
    (module-section "cryptovampire/solver" solver-fns solver-syntax)
    (module-section "cryptovampire/cryptography" cryptography-fns '())
    (module-section "cryptovampire/signature" '() signature-syntax)))

(displayln "wrote docs/scheme-api.md")
