;; This file provides common tooling accross all examples, notably how to write
;; out the results to a csv
(provide run-and-save)
(require-builtin cryptovampire/ll/pbl as pbl->)
(require-builtin cryptovampire/ll/report as report->)
(require-builtin cryptovampire/ll/configuration as config->)
(require-builtin cryptovampire/ll as b.)


(define (print-row file . args)
  (begin
    (for-each (lambda (x)
        (begin
          (cond
            [ (string? x) (write-string x file) ]
            [ (b.duration? x) (write (b.duration->millis x) file) ]
            [else (write x file) ])
          (write-string "," file)))
      args)
    (write-string "\n" file)))

(define (prepare file)
  (if (path-exists? file)
    (let [ (content (read-port-to-string (open-input-file file))) (file (open-output-file file)) ]
      (begin
        (write-string content file)
        file))
    (let [ (file (open-output-file file)) ]
      (begin
        (print-row file "name" "runtime" "vampire time" "max smt" "total" "hits" "hitrate" "timeout")
        file))))
(define get-file (let [ (env (maybe-get-env-var "RESULT")) ]
    (if (Err? env) "/tmp/results.csv" (Ok->value env))))

(define scale-timeout (let [ (env (maybe-get-env-var "SCALE_TIMEOUT")) ]
    (if (Err? env) 1.0 (string->number (Ok->value env)))))

(define (save-results name pbl)
  (let* [
    (file (prepare get-file))
    (report (pbl->get-report pbl))
    (runtime (report->get-runtime report))
    (vampire (report->get-smt-time report))
    (max-smt (report->get-max-smt-time report))
    (hits (report->get-total-cache-hits report))
    (total (report->get-total-run-calls report))
    (hit-rate (report->get-hit-rate report))
    (vampire-timeout (config->get_smt_timeout pbl))
    ]
    (print-row file name runtime vampire max-smt total hits hit-rate vampire-timeout)))

(define (run-and-save name pbl p1 p2 duration)
  (begin
    (config.set_smt_timeout pbl
      (b.mult->duration scale-timeout (b.string->duration "150ms")))
    (if (run pbl p1 p2)
      (displayln "success")
      (error (string-append "failed" name)))
    (displayln (report.print-report (pbl.get-report pbl)))
    (save-results name pbl)))
