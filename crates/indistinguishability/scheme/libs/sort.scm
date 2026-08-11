(provide
  Nonce Bool Bitstring Message Time Protocol Step Index Any Condition
  Nonce? Bool? Bitstring? Message? Time? Protocol? Step? Index? Any? Condition?
)
(require-builtin cryptovampire/ll/sort as sort->)

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

(define Bool sort->Bool)
(define Bool? sort->Sort-Bool?)

(define Bitstring sort->Bitstring)
(define Bitstring? sort->Sort-Bitstring?)

;; messages sent on the wire are bitstrings
(define Message Bitstring)
(define Message? Bitstring?)

(define Time sort->Time)
(define Time? sort->Sort-Time?)

(define Protocol sort->Protocol)
(define Protocol? sort->Sort-Protocol?)

;; a step is identified by the time at which it happens
(define Step Time)
(define Step? Time?)

(define Index sort->Index)
(define Index? sort->Sort-Index?)

(define Any sort->Any)
(define Any? sort->Sort-Any?)

(define Condition Bool)
(define Condition? Bool?)
