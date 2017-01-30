#lang racket

;; ;; Alternate implementation using the heavier-weight racket/sandbox, in case
;; ;; racket/engine ceases to exist.
;; (require racket/sandbox)
;; (define (timeout timeout-secs thunk) (with-limits timeout-secs #f (thunk)))

(require racket/engine syntax/parse/define)

(provide timeout with-timeout)

(define (timeout
         timeout-secs
         thunk
         #:on-success [on-success identity]
         #:on-timeout [on-timeout (lambda () (error "timeout"))])
  (define thunk-result #f)
  (define eng (engine (lambda (_ignored:disable-suspends) (thunk))))
  ;; NB. engine-run will raise an exception if `run-thunk` does.
  (if (engine-run (* 1000 timeout-secs) eng)
    (on-success (engine-result eng))
    (on-timeout)))

(define-syntax-parser with-timeout
  [(_ timeout-secs body ...)
   #'(timeout timeout-secs (lambda () body ...))])
