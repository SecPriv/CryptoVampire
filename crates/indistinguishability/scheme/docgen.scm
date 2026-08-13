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
;;                   from their unwrapped Rust functions);
;;   * the low-level rust bindings (`cryptovampire/ll/*`) -- the functions are
;;                   listed by hand below; their docs are the Rust doc comments
;;                   (`#%native-fn-ptr-doc->string`).  Functions without a doc
;;                   comment are still listed (with an empty body).
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

(require-builtin cryptovampire/ll/pbl as pbl->)
(require-builtin cryptovampire/ll/formula as llformula->)
(require-builtin cryptovampire/ll/function as llfunction->)
(require-builtin cryptovampire/ll/signature as llsignature->)
(require-builtin cryptovampire/ll/variable as llvariable->)
(require-builtin cryptovampire/ll/alias as llalias->)
(require-builtin cryptovampire/ll/rewrite as llrewrite->)
(require-builtin cryptovampire/ll/rule as llrule->)
(require-builtin cryptovampire/ll/step as llstep->)
(require-builtin cryptovampire/ll/cryptography as llcrypto->)
(require-builtin cryptovampire/ll/report as llreport->)
(require-builtin cryptovampire/ll/configuration as llconf->)

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
;; the low-level rust bindings (cryptovampire/ll/*) -- (name . value) pairs,
;; listed by hand.  Their docs are the Rust doc comments; functions without
;; one are still listed (with an empty body).
;; ---------------------------------------------------------------------------

(define ll-pbl-fns
  (list
    (cons 'run pbl->run)
    (cons 'empty pbl->empty)
    (cons 'declare-function pbl->declare-function)
    (cons 'declare-protocol pbl->declare-protocol)
    (cons 'declare-memory-cell pbl->declare-memory-cell)
    (cons 'declare-exists pbl->declare-exists)
    (cons 'add-rule pbl->add-rule)
    (cons 'add-rewrite pbl->add-rewrite)
    (cons 'add-smt-axiom pbl->add-smt-axiom)
    (cons 'add-constrain pbl->add-constrain)
    (cons 'publish pbl->publish)
    (cons 'get-report pbl->get-report)
    (cons 'get-all-protocols pbl->get-all-protocols)
    (cons 'get-all-steps pbl->get-all-steps)))

(define ll-formula-fns
  (list
    (cons 'binder llformula->binder)
    (cons 'var llformula->var)
    (cons 'app llformula->app)
    (cons 'destruct llformula->destruct)
    (cons 'cand llformula->cand)
    (cons 'cor llformula->cor)
    (cons 'ctuple llformula->ctuple)
    (cons 'binder->exists llformula->binder->exists)
    (cons 'binder->forall llformula->binder->forall)
    (cons 'binder->findst llformula->binder->findst)
    (cons 'get-sort llformula->get_sort)))

(define ll-function-fns
  (list
    (cons 'mk-function llfunction->mk-function)
    (cons 'mk-nonce llfunction->mk-nonce)
    (cons 'mk-alias llfunction->mk-alias)
    (cons 'name llfunction->name)
    (cons 'signature llfunction->signature)))

(define ll-signature-fns
  (list
    (cons 'new llsignature->new)
    (cons 'inputs llsignature->inputs)
    (cons 'output llsignature->output)))

(define ll-variable-fns
  (list
    (cons 'fresh-with-sort llvariable->fresh-with-sort)
    (cons 'fresh llvariable->fresh)))

(define ll-alias-fns
  (list
    (cons 'new-rewrite llalias->new-rewrite)
    (cons 'rewrite-from llalias->rewrite-from)
    (cons 'rewrite-to llalias->rewrite-to)
    (cons 'rewrite-variables llalias->rewrite-variables)))

(define ll-rewrite-fns
  (list (cons 'new llrewrite->new)))

(define ll-rule-fns
  (list (cons 'new-prolog llrule->new-prolog)))

(define ll-step-fns
  (list
    (cons 'declare-step llstep->declare-step)
    (cons 'declare-exists llstep->declare-exists)
    (cons 'get-vars llstep->get-vars)
    (cons 'get-msg llstep->get-msg)
    (cons 'get-cond llstep->get-cond)
    (cons 'set-msg llstep->set-msg)
    (cons 'set-cond llstep->set-cond)
    (cons 'string llstep->string)
    (cons 'mk-single-assignment llstep->mk-single-assignment)
    (cons 'insert-assignement llstep->insert-assignement)))

(define ll-cryptography-fns
  (list
    (cons 'declare-cryptography llcrypto->declare-cryptography)
    (cons 'register-fresh-nonce llcrypto->register-fresh-nonce)
    (cons 'init->prf llcrypto->init->prf)
    (cons 'init->ddh llcrypto->init->ddh)
    (cons 'init->aenc llcrypto->init->aenc)
    (cons 'init->senc llcrypto->init->senc)
    (cons 'init->xor llcrypto->init->xor)))

(define ll-report-fns
  (list
    (cons 'print-report llreport->print-report)
    (cons 'get-hit-rate llreport->get-hit-rate)
    (cons 'get-smt-time llreport->get-smt-time)
    (cons 'get-runtime llreport->get-runtime)
    (cons 'get-total-run-calls llreport->get-total-run-calls)
    (cons 'get-total-cache-hits llreport->get-total-cache-hits)
    (cons 'get-tested-nonces llreport->get-tested-nonces)
    (cons 'get-max-smt-time llreport->get-max-smt-time)))

;; configuration accessors (get_/set_ pairs over the `Configuration` options)
(define ll-configuration-fns
  (list
    (cons 'get_trace llconf->get_trace)
    (cons 'set_trace llconf->set_trace)
    (cons 'get_cores llconf->get_cores)
    (cons 'set_cores llconf->set_cores)
    (cons 'get_prf_limit llconf->get_prf_limit)
    (cons 'set_prf_limit llconf->set_prf_limit)
    (cons 'get_fa_limit llconf->get_fa_limit)
    (cons 'set_fa_limit llconf->set_fa_limit)
    (cons 'get_ddh_limit llconf->get_ddh_limit)
    (cons 'set_ddh_limit llconf->set_ddh_limit)
    (cons 'get_enc_kp_limit llconf->get_enc_kp_limit)
    (cons 'set_enc_kp_limit llconf->set_enc_kp_limit)
    (cons 'get_smt_timeout llconf->get_smt_timeout)
    (cons 'set_smt_timeout llconf->set_smt_timeout)
    (cons 'get_keep_smt_files llconf->get_keep_smt_files)
    (cons 'set_keep_smt_files llconf->set_keep_smt_files)
    (cons 'get_trace_rebuilds llconf->get_trace_rebuilds)
    (cons 'set_trace_rebuilds llconf->set_trace_rebuilds)
    (cons 'get_trace_guessed_published_nonces llconf->get_trace_guessed_published_nonces)
    (cons 'set_trace_guessed_published_nonces llconf->set_trace_guessed_published_nonces)
    (cons 'get_guided_nonce_search llconf->get_guided_nonce_search)
    (cons 'set_guided_nonce_search llconf->set_guided_nonce_search)
    (cons 'get_egg_iter_limit llconf->get_egg_iter_limit)
    (cons 'set_egg_iter_limit llconf->set_egg_iter_limit)
    (cons 'get_egg_timeout llconf->get_egg_timeout)
    (cons 'set_egg_timeout llconf->set_egg_timeout)
    (cons 'get_egg_node_limit llconf->get_egg_node_limit)
    (cons 'set_egg_node_limit llconf->set_egg_node_limit)))

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

;; Render every listed function whether or not it has a doc (rust bindings).
;; Rust doc comments start straight with the text (no cv-help title line to
;; strip).
(define (ll-fns-section pairs)
  (apply string-append
    (map
      (lambda (p)
        (let ((name (symbol->string (car p))) (f (cdr p)))
          (let ((d (raw-doc f)))
            (string-append
              "\n#### " name "\n\n" (if d d "") "\n"))))
      pairs)))

(define (ll-module-section title pairs)
  (doc-put
    (string-append "\n## " title "\n\n### Functions\n" (ll-fns-section pairs))))

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
    (module-section "cryptovampire/builtin-functions" '() builtin-doc)

    ;; the low-level rust bindings
    (doc-put "\n# Rust bindings (`cryptovampire/ll`)\n")
    (ll-module-section "cryptovampire/ll/pbl" ll-pbl-fns)
    (ll-module-section "cryptovampire/ll/formula" ll-formula-fns)
    (ll-module-section "cryptovampire/ll/function" ll-function-fns)
    (ll-module-section "cryptovampire/ll/signature" ll-signature-fns)
    (ll-module-section "cryptovampire/ll/variable" ll-variable-fns)
    (ll-module-section "cryptovampire/ll/alias" ll-alias-fns)
    (ll-module-section "cryptovampire/ll/rewrite" ll-rewrite-fns)
    (ll-module-section "cryptovampire/ll/rule" ll-rule-fns)
    (ll-module-section "cryptovampire/ll/step" ll-step-fns)
    (ll-module-section "cryptovampire/ll/cryptography" ll-cryptography-fns)
    (ll-module-section "cryptovampire/ll/report" ll-report-fns)
    (ll-module-section "cryptovampire/ll/configuration" ll-configuration-fns)))

(displayln "wrote docs/scheme-api.md")
