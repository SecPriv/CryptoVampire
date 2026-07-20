; Comments stolen from squirrel

; Not supported

; (*******************************************************************************
; YUBIHSM
;
; [1] R. Künnemann, "Foundations for analyzing security APIs in the symbolic and
; computational model", 2014.
;
; Y   -> S   : <pid,<nonce,otp>>
; S   -> HSM : <<pid,kh>,<aead,otp>>
; HSM -> S   : ctr
; S   -> Y   : accept
;
; with
; - aead = enc(<k,pid,sid>,mkey)
; - otp = enc(<sid,ctr>,npr,k)
;
; PUBLIC DATA
; - kh, pid
; SECRET DATA KNOWN BY EACH PARTY
; - YubiKey(pid): k(pid), sid(pid), ctr(pid)
; - Server: { sid(pid), ctr(pid) | pid }
; - HSM: mkey, { k(pid), sid(pid) | pid }
;
; COMMENTS
; - The last message "otp || nonce || hmac || status" is unclear and
;   not modelled at all and replaced by "accept".
;   It was also not modelled in [1].
;
; - The otp is an encryption of a triple (sid, ctr, npr).
;   It is modelled here as a randomized encryption of a pair (sid, ctr).
;
; - enc is assumed to be AEAD (we do not use the associated data).
;
; - In [1], they "over-approximate in the case that the Yubikey increases the
;   session token by allowing the adversary to instantiate the rule for any
;   counter value that is higher than the previous one".
;   Here, we model the incrementation by 1 of the counter.
;
; - As in [1], we model the two counters (session and token counters) as a single
;   counter.
;
; - In [1], the server keeps in memory the mapping between public and
;   secret identities of the Yubikeys. As far as we understand, this
;   does not reflect the YubiHSM specification: secret identities have  to
;   be protected by the YubiHSM.  Instead, we choose to keep the
;   necessary information to map public to private identities in the
;   AEADs (we simply add the public identity to the AEADs plaintext).
;
; - Diff terms are here to model a real system and an ideal system.
;   The purpose of the ideal system is to replace the key inside the AEAD by a
;   dummy one, in order to be able to use the intctxt tactic for the third
;   security property (injective correspondence).
;
; HELPING LEMMAS
; - counter increase
; - valid decode
;
; SECURITY PROPERTIES
; The 3 security properties as stated in [1].
; - Property 1: no replay counter
; - Property 2: injective correspondence
; - Property 3: monotonicity
;
; Properties 1 and 3 are established directly on the real system.
; Property 2 is proved in 2 steps: first an equivalence is established
; between the real system and the ideal one, and then the property
; is proved on the ideal system. The reach equiv
; tactic allows one to combine these two steps, and to conclude.
; *******************************************************************************)

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

(displayln "skipping.")
(b.exit 0)

(define pbl (mk-problem 'x))

(define p1 (declare-protocol pbl))
(define p2 (declare-protocol pbl))

(define senc (declare-cryptography pbl))

(define-function enc pbl (senc) (Bitstring Bitstring Bitstring) -> Bitstring)
(define-function dec pbl (senc) (Bitstring Bitstring) -> Bitstring)

(define-function mkey pbl Nonce)
(define-function rinit pbl (Index) -> Nonce)
(define-function kh pbl Bitstring)
(define-function mpid pbl (Index) -> Bitstring)
(define-function sid pbl (Index) -> Nonce)
(define-function k pbl (Index) -> Nonce)
(define-function k-dummy pbl (Index) -> Nonce)
(define-function cinit pbl Bitstring)
(define-function mySucc pbl (Bitstring) -> Bitstring)
(define-function endplug pbl Bitstring)
(define-function accept pbl Bitstring)
(define-function setup-ok pbl Bitstring)
(define-function npr pbl (Index Index) -> Nonce)
(define-function ilt pbl (Bitstring Bitstring) -> Bool)

(define YCtr (declare-memory-cell pbl "YCtr" (list Index) (lambda (_ i) cinit)))
(define SCtr (declare-memory-cell pbl "SCtr" (list Index) (lambda (_ i) cinit)))
(define AEAD (declare-memory-cell pbl "AEAD" (list Index) (lambda (_ pid)
      (enc (tuple (k pid) (tuple (mpid pid) (sid pid))) (rinit pid) mkey))))

(define Setup (declare-same-step pbl "Setup" (list p1 p2) (list Index)
    (lambda _ mtrue)
    (lambda (p in pid . _) accept)
    empty-assignements))

(define Plug (declare-step pbl "Plug" (list Index Index)
    (step p1
      (lambda (in pid j cells . _)
        (eq in endplug))
      (lambda (in pid j cells . _) endplug)
      (lambda (in pid j cells . _)
        (list (store-cell ((_) YCtr pid) := (mySucc (cells YCtr pid)))) ;
      ))
  (step p2
    (lambda _ mtrue)
    (lambda (in pid j cells . _) endplug)
    (lambda (in pid j cells . _)
      (list (store-cell ((_) YCtr pid) := (mySucc (cells YCtr pid))))))))

(define Press (declare-step pbl "Press" (list Index Index)
    (step p1
      (lambda _ mtrue)
      (lambda (in pid j cells . _)
        (let ((ctr (cells YCtr)))
          (tuple (mpid pid)
            (tuple (nonce pid j)
              (enc (tuple (sid pid) ctr) (npr pid j) (k pid))))))
      (lambda (in pid j cells . _)
        (list (store-cell ((_) YCtr pid) := (mySucc (cells YCtr pid))))))
    (step p2
      (lambda _ mtrue)
      (lambda (in pid j cells . _)
        (let [ (ctr (cells YCtr)) ]
          (tuple (mpid pid)
            (tuple (nonce pid j)
              (enc (tuple (sid pid) ctr) (npr pid j) (k-dummy pid))))))
      (lambda (in pid j cells . _)
        (list (store-cell ((_) YCtr pid) := (mySucc (cells YCtr pid))))))))

; (define Server (declare-step pbl "Server" (list Index Index)
;     (step p1
;       (lambda (in pid j cells . _)
;         (let ((deccipher (dec (sel2of2 (sel2of2 in)) (k pid))))
;           (cand
;             (eq (sel1of2 in) (mpid pid))
;             (not (eq deccipher fail))
;             (eq (sel1of2 deccipher) (sid pid))
;             (ilt (cells SCtr) (sel2of2 deccipher)))))
;       (lambda (in pid j cells . _) accept)
;       (lambda (in pid j cells . _)
;         (let ((deccipher (dec (sel2of2 (sel2of2 in)) (k pid))))
;           (list (store-cell (SCtr pid) := (sel2of2 deccipher))))))
;     (step p2
;       (lambda (in pid j cells . _)
;         (let ((deccipher (dec (sel2of2 (sel2of2 in)) (k-dummy pid))))
;           (cand
;             (eq (sel1of2 in) (mpid pid))
;             (not (eq deccipher fail))
;             (eq (sel1of2 deccipher) (sid pid))
;             (ilt (cells SCtr) (sel2of2 deccipher)))))
;       (lambda (in pid j cells . _) accept)
;       (lambda (in pid j cells . _)
;         (let ((deccipher (dec (sel2of2 (sel2of2 in)) (k-dummy pid))))
;           (list (store-cell (SCtr pid) := (sel2of2 deccipher))))))))

; (define Decode (declare-step pbl "Decode" (list Index Index)
;     (step p1
;       (lambda (in pid j cells . _)
;         (let ((aead-dec (dec (sel1of2 (sel2of2 in)) mkey))
;             (otp-dec (dec (sel2of2 (sel2of2 in)) (k pid))))
;           (cand
;             (eq (sel1of2 in) (tuple (mpid pid) kh))
;             (not (eq aead-dec fail))
;             (not (eq otp-dec fail))
;             (eq (sel1of2 otp-dec) (sel2of2 (sel2of2 aead-dec)))
;             (eq (mpid pid) (sel1of2 (sel2of2 aead-dec))))))
;       (lambda (in pid j cells . _)
;         (sel2of2 (dec (sel2of2 (sel2of2 in)) (k pid))))
;       empty-assignements)
;     (step p2
;       (lambda (in pid j cells . _)
;         (let ((aead-dec (dec (sel1of2 (sel2of2 in)) mkey))
;             (otp-dec (dec (sel2of2 (sel2of2 in)) (k-dummy pid))))
;           (cand
;             (eq (sel1of2 in) (tuple (mpid pid) kh))
;             (not (eq aead-dec fail))
;             (not (eq otp-dec fail))
;             (eq (sel1of2 otp-dec) (sel2of2 (sel2of2 aead-dec)))
;             (eq (mpid pid) (sel1of2 (sel2of2 aead-dec))))))
;       (lambda (in pid j cells . _)
;         (sel2of2 (dec (sel2of2 (sel2of2 in)) (k-dummy pid))))
;       empty-assignements)))

(initialize-as-senc senc enc dec)

(pbl.add-smt-axiom pbl (forall ((n Bitstring))
    (not (eq n (mySucc n)))))

(pbl.add-smt-axiom pbl (forall ((n1 Bitstring) (n2 Bitstring))
    (=> (and (ilt n1 n2) (ilt n2 (mySucc n1)))
      false)))

(pbl.add-smt-axiom pbl (forall ((pid Index) (pid2 Index))
    (=> (eq (mpid pid) (mpid pid2))
      (idx-eq pid pid2))))

(config.set_smt_timeout pbl (b.mult->duration scale-timeout (b.string->duration "1s")))
(config.set_fa_limit pbl 2)

; (if (run pbl p1 p2)
;   (displayln "success")
;   (error "failed yubihsm"))

; (displayln (report.print-report (pbl.get-report pbl)))
; (save-results "yubihsm" pbl)

