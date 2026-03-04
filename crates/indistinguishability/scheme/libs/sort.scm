(provide 
  Nonce Bool Bitstring Message Time Protocol Step Index Any Condition
  Nonce? Bool? Bitstring? Message? Time? Protocol? Step? Index? Any? Condition?
  )
(require-builtin cryptovampire/ll/sort as sort->)

(define Nonce sort->Nonce)
(define Nonce? sort->Sort-Nonce?)

(define Bool sort->Bool)
(define Bool? sort->Sort-Bool?)

(define Bitstring sort->Bitstring)
(define Bitstring? sort->Sort-Bitstring?)

(define Message Bitstring)
(define Message? Bitstring?)

(define Time sort->Time)
(define Time? sort->Sort-Time?)

(define Protocol sort->Protocol)
(define Protocol? sort->Sort-Protocol?)

(define Step Time)
(define Step? Time?)

(define Index sort->Index)
(define Index? sort->Sort-Index?)

(define Any sort->Any)
(define Any? sort->Sort-Any?)

(define Condition Bool)
(define Condition? Bool?)