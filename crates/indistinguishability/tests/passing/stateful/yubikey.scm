(require "../save-results.scm")
(require "cryptovampire/function")
(require "cryptovampire/builtin-functions")
(require "cryptovampire/cryptography")
(require "cryptovampire/protocol")
(require "cryptovampire/solver")
(require "cryptovampire/sort")
(require "cryptovampire/formula")
(require "cryptovampire/signature")
(require-builtin cryptovampire/ll/pbl as pbl.)
(require-builtin cryptovampire/ll/configuration as config.)
(require-builtin cryptovampire/ll as b.)
(require-builtin cryptovampire/ll/report as report.)
(require-builtin cryptovampire/ll/builtin-functions as builtin.)

(define pbl (mk-problem 'x))

(define p1 (declare-protocol pbl))
(define p2 (declare-protocol pbl))

(define senc (declare-cryptography pbl))

(define-function enc pbl (senc) (Bitstring Bitstring Bitstring) -> Bitstring)
(define-function dec pbl (senc) (Bitstring Bitstring) -> Bitstring)
(define-function k pbl (Index) -> Nonce)
(define-function sid pbl (Index) -> Nonce)
(define-function pid pbl (Index) -> Bitstring)
(define-function nonce pbl (Index Index) -> Nonce)
(define-function npr pbl (Index Index) -> Nonce)
(define-function myzero pbl Bitstring)
(define-function mySucc pbl (Bitstring) -> Bitstring)
(define-function startplug pbl Bitstring)
(define-function endplug pbl Bitstring)
(define-function accept pbl Bitstring)

(define YCpt (declare-memory-cell pbl "YCpt" (list Index) (lambda (i) myzero)))
(define SCpt (declare-memory-cell pbl "SCpt" (list Index) (lambda (i) myzero)))

(define yubikeyplug (declare-step pbl "yubikeyplug" (list Index Index)
    (step p1
      (lambda (p in i j cells . _)
        (eq in startplug))
      (lambda (p in i j cells . _) endplug)
      (lambda (in i j cells . _)
        (list (store-cell (YCpt i) := (mySucc (cells YCpt))))))))

(define yubikeypress (declare-step pbl "yubikeypress" (list Index Index)
    (step p1
      (lambda _ mtrue)
      (lambda (in i j cells . _)
        (let ((ctr (mySucc (cells YCpt))))
          (enc (tuple (sid i) ctr) (npr i j))))
      (lambda (in i j cells . _)
        (list (store-cell (YCpt i) := (mySucc (cells YCpt)))))))

(define server (declare-step pbl "server" (list Index)
    (step p1
      (lambda (p in i cells . _)
        (let ((decrypted (dec in (k i))))
          (cand
            (eq (sel1of2 decrypted) (sid i))
            (lt (cells SCpt) (sel2of2 decrypted)))))
      (lambda (p in i cells . _) accept)
      (lambda (p in i cells . _)
        (let ((decrypted (dec in (k i))))
          (list (store-cell (SCpt i) := (sel2of2 decrypted)))))))

(initialize-as-senc senc enc dec)

(pbl.add-smt-axiom pbl (forall ((n Bitstring))
  (not (eq n (mySucc n)))))

(pbl.add-smt-axiom pbl (forall ((n1 Bitstring) (n2 Bitstring))
  (=> (and (lt n1 n2) (lt n2 (mySucc n1)))
    false)))

(config.set_smt_timeout pbl (b.mult->duration scale-timeout (b.string->duration "500ms")))
(config.set_fa_limit pbl 2)

(if (run pbl p1 p2)
  (displayln "success")
  (error "failed yubikey"))

(displayln (report.print-report (pbl.get-report pbl)))
(save-results "yubikey" pbl)
