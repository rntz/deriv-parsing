#lang racket

;; Provides lazy trees, an interface supporting enumeration by iterative
;; deepening.

(provide lazytree? lazytree/c lazytree
         empty-lazytree lazyleaf lazynode
         in-lazytree lazytree->list lazytree->stream
         stream->lazytree list->lazytree sequence->lazytree)

(require "util.rkt")

;; A lazytree is a thunk that returns (values elems children)
;; - elems is a stream of values
;; - children is a list of child trees
;;
;; A thunk is a 0-argument function, NOT a promise. Promises remember their
;; values when they're forced, which is the opposite of what we want for
;; iterative deepening.
(define lazytree? procedure?)
(define lazytree/c
  (recursive-contract
   (-> (values stream? (listof lazytree/c)))))

;; I should think of what a good interface for generating lazytrees is. are they
;; naturally monadic? they're certainly applicative. is for/lazytree possible
;; without compromising on laziness?

(define-syntax-rule (lazytree elems children)
  (lambda () (values elems children)))

(define empty-lazytree (lazytree '() '()))
(define-syntax-rule (lazyleaf x ...)  (lazytree (list x ...) '()))
(define-syntax-rule (lazynode xs ...) (lazytree '() (list xs ...)))

(define (stream->lazytree s) (lazytree s '()))
(define (list->lazytree s)   stream->lazytree)
(define (sequence->lazytree s) (stream->lazytree (sequence->stream s)))

(define (lazytree->list tree)   (sequence->list (in-lazytree tree)))
(define (lazytree->stream tree) (sequence->stream (in-lazytree tree)))

;; Iterative deepening.
(define (in-lazytree tree)
  (in-generator
   (let loop ([depth 0])
     (when (explore depth tree)
       (loop (+ depth 1))))))

;; Runs inside a generator. yields elements in `tree' at `depth', then returns
;; #t if `tree' has subtrees left to be explored below `depth'.
(define (explore depth tree)
  (define-values (elems children) (tree))
  (match depth
    [0 (for ([e elems]) (yield e))
       (not (null? children))]
    [_ (define continue #f)
       (for ([c children])
         (when (explore (- depth 1) c)
           (set! continue #t)))
       continue]))


(module+ test
  (require rackunit "timeout.rkt")

  (define nats
    (let loop ([i 0])
      (lazytree (list i) (list (loop (+ 1 i))))))
  (check-equal?
   '(0 1 2 3 4 5 6 7 8 9)
   (stream-take 10 (lazytree->stream nats)))

  (define ab-leaf (lazyleaf 'a 'b))
  (define ab-node (lazynode (lazyleaf 'a) (lazyleaf 'b)))
  (check-equal? '(a b) (lazytree->list ab-leaf))
  (check-equal? '(a b) (lazytree->list ab-node))

  (define nats-or-hello
    (lazynode nats (lazyleaf 'hello)))
  (define hello (stream-take 10 (lazytree->stream nats-or-hello)))
  (check-not-false (member 'hello hello))

  (define infloop (lazytree '() (list infloop)))
  (define joy-or-infloop (lazynode infloop (lazyleaf 'joy)))
  (check-equal? '(joy)
                (with-timeout 1
                  (stream-take 1 (lazytree->stream joy-or-infloop))))

  )
