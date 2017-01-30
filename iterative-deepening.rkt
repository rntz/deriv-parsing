#lang racket

(provide lazytree? lazytree/c lazytree
         empty-lazytree lazyleaf lazynode
         in-lazytree lazytree->list lazytree->stream
         stream->lazytree list->lazytree sequence->lazytree)

(require "util.rkt")

;; a lazytree is a thunk that returns (values elems children)
;; - elems is a stream of values
;; - children is a list of child trees
;;
;; a thunk is a 0-argument function, NOT a promise. promises remember their
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

;; uses iterative deepening.
(define (in-lazytree tree)
  (in-generator
   (let loop ([depth 0])
     (define g (generator () (explore depth tree)))
     (let consume ()
       (define x (g))
       (match (generator-state g)
         ['done
          ;; `x` is #t iff we are done.
          (unless x (loop (+ depth 1)))]
         ['suspended
          ;; `x` is a list of elements.
          (for ([elem x]) (yield elem))
          (consume)]
         [_ (error "generator in impossible state")])))))

;; meant to be run inside a generator.
;;
;; yields lists of elements in `tree' at `depth', then returns #t if `tree' has
;; no subtrees left to be explored below `depth'.
(define (explore depth tree)
  (define-values (elems children) (tree))
  (match depth
    [0 (yield elems)
       (null? children)]
    [_ (for/fold ([done #t]) ([c children])
         ;; NB. It is extremely critical that the first argument to (and) be the
         ;; call to (explore), because (explore) is side-effectful, and we wish
         ;; to run it even if `done' is #t!
         (and (explore (- depth 1) c) done))]))


(module+ test
  ;; TODO real tests
  (define nats
    (let loop ([i 0])
      (lazytree (list i) (list (loop (+ 1 i))))))

  (define nats-or-hello
    (lazynode nats (lazyleaf 'hello))))
