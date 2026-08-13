(provide
  Nonce Bool Bitstring Message Time Protocol Step Index Any Condition
  Nonce? Bool? Bitstring? Message? Time? Protocol? Step? Index? Any? Condition?
  sort-doc
)
(require-builtin cryptovampire/ll/sort as sort->)
(require "cryptovampire/doc")

;; Documentation table for the `cryptovampire/sort` library (value docs, next
;; to their definitions).  See `cryptovampire/doc` for the mechanism.
(define sort-doc (make-doc-table))
(define (register-syntax-doc! name . doc)
  (set! sort-doc (apply doc-add! sort-doc name doc)))
(define (register-type-doc! name . doc)
  (set! sort-doc (apply doc-add! sort-doc name doc)))

;; ---------------------------------------------------------------------------
;; Sorts.
;;
;; The `cryptovampire/sort` module re-exports the *sort* values that every
;; signature, variable and function is typed with.  They are plain values
;; (there is no `help` documentation for them, but their meaning is their name):
;;
;;   Nonce Bitstring Bool Time Protocol Index Any
;;
;; Plus the friendly aliases:
;;   Message   == Bitstring      (protocol messages are bitstrings)
;;   Step      == Time           (steps happen at a time)
;;   Condition == Bool
;;
;; Current sorts are then matched with the `?` predicates, e.g. `(Nonce? x)`.
;; ---------------------------------------------------------------------------

(define Nonce sort->Nonce)
(define Nonce? sort->Sort-Nonce?)

(register-type-doc! 'Nonce
  "A fresh nonce: an unpredictable value used once, typically as a key or seed."
  "A function returning a `Nonce` gets wrapped (`wrap-nonce`) so it can be called in terms.")

(define Bool sort->Bool)
(define Bool? sort->Sort-Bool?)

(register-type-doc! 'Bool
  "The boolean sort.  Formula combinators such as `cand`, `cor`, `eq`, `lt` build `Bool` formulas.")

(define Bitstring sort->Bitstring)
(define Bitstring? sort->Sort-Bitstring?)

(register-type-doc! 'Bitstring
  "Raw bitstrings, the sort of messages.  Most cryptographic operations (hashing, encryption, xor, exponentiation) map bitstrings to bitstrings.")

;; messages sent on the wire are bitstrings
(define Message Bitstring)
(define Message? Bitstring?)

(register-type-doc! 'Message
  "Alias of `Bitstring`: messages sent on the wire are bitstrings.")

(define Time sort->Time)
(define Time? sort->Sort-Time?)

(register-type-doc! 'Time
  "Times, used to order steps (`lt`, `leq`, `pred`, ...).  The `Step` of a step is the time at which it happens.")

(define Protocol sort->Protocol)
(define Protocol? sort->Sort-Protocol?)

(register-type-doc! 'Protocol
  "A protocol (a participant).  Declared with `declare-protocol`; steps and memory cells are instantiated per protocol.")

;; a step is identified by the time at which it happens
(define Step Time)
(define Step? Time?)

(register-type-doc! 'Step
  "Alias of `Time`.  A step is identified by the time at which it happens.")

(define Index sort->Index)
(define Index? sort->Sort-Index?)

(register-type-doc! 'Index
  "An index, used to range over repetitions (protocol runs, list elements, ...).  Binds fresh in `bind`, `exists`, `publish`, step declarations, ...")

(define Any sort->Any)
(define Any? sort->Sort-Any?)

(register-type-doc! 'Any
  "The top/unknown sort, used when a term's sort is not (yet) fixed.")

(define Condition Bool)
(define Condition? Bool?)

(register-type-doc! 'Condition
  "Alias of `Bool`: the sort of step run-conditions.")
