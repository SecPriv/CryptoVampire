(provide
  save-results)
(require-builtin cryptovampire as cv-)
(require-builtin "steel/base")


(define (print-row file . args)
  (begin
    (for-each (lambda (x)
        (begin
          (if (string? x)
            (write-string x file)
            (if (cv-duration? x)
              (write (duration->millis x) file)
              (write x file)))
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
        (print-row file "name" "runtime" "vampire time" "total" "hits" "hitrate")
        file))))

(define (save-results file name pbl)
  (let* [
    (file (prepare file))
    (report (cv-get-report pbl))
    (runtime (cv-get-runtime report))
    (vampire (cv-get-time-spent-in-vampire report))
    (hits (cv-get-total-cache-hits report))
    (total (cv-get-total-run-calls report))
    (hit-rate (cv-get-hit-rate report)) ]
    (print-row file name runtime vampire total hits hit-rate)))
