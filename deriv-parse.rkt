#lang racket

(require "util.rkt")

;; ==================== Utilities ====================

;; returns whether the (mutable) set already has the element.
(define (set-add?! st v)
  (if (set-member? st v) #t
      (begin0 #f (set-add! st v))))

;; Takes the cartesian product of a list of sets. For example:
;;
;;     > (sets-product (list (set 1 2) (set 'a 'b)))
;;     (set '(1 b) '(1 a) '(2 b) '(2 a))
;;
(define/contract (sets-product sets)
  (-> (listof set?) set?)
  ;; we reverse the sets so that we don't have to reverse the accumulated list
  ;; at the end.
  (let loop ([sets (reverse sets)] [acc '()])
    (match sets
      ['() (set acc)]
      [(cons s sets)
       (set-unions
        (for/list ([elem s])
          (loop sets (cons elem acc))))])))

;; This maps a function `f' across the cartesian product of a list of sets,
;; producing a set of results.
;; `f' must accept N arguments, where N is the number of sets.
(define (sets-map f sets)
  (for/set ([x (sets-product sets)])
    (apply f x)))

;; n-ary version of sets-map
(define (set-map* f . sets) (sets-map f sets))


;; =============== Parser structures & constructors ===============
(enum concrete-parser
  ;; a recursive parser is a unique identifier plus a thunk that computes its
  ;; body. TODO: implement this way of thinking about it
  ;; (p-rec ident thunk)
  (p-eps* results)
  (p-lit tokens)
  (p-one-of parsers)
  (p-apply func parsers))

(define parser? (or/c promise? concrete-parser?))
(define parser/c (or/c (promise/c concrete-parser?) concrete-parser?))

(define (p-eps x) (p-eps* (set x)))
(define (p-tok t) (p-lit (list t)))
(define (p-or . ps) (p-one-of ps))
(define p-empty (p-or))
(define (p-map f . parsers) (p-apply f parsers))

(define (p-first p . ps) (p-apply first (cons p ps)))
(define (p-last p . ps) (p-apply last (cons p ps)))
(define (p-list . ps) (p-apply list ps))


;; =============== Running parsers ===============
;; relies on functions defined below, under "Core parsing code"
(define (parse p toks)
  (match toks
    ['() (parse-null p)]
    [(cons tok toks) (parse (p-derive p tok) toks)]))


;; =============== Syntax sugar ===============
(require (for-syntax syntax/parse))

(define-syntax lang
  (syntax-parser
    [(_ e) (lang-parse #'e)]
    [(_ e ...) (lang-parse #'(begin e ...))]))

(define-for-syntax lang-parse
  (syntax-parser
    #:datum-literals (eps pure quote ? empty escape -->)
    #:literals (begin0 begin or)
    [e:id #'e]
    [((~or eps pure) v ...) #'(p-eps* (set v ...))]
    ;; TODO: maybe quote should be used for tokens?
    ;; and '? should be used for class? dunno.
    [(quote x) #'(p-tok 'x)]
    ;; alternation
    [empty          #'p-empty]
    [(or p ...)     #'(p-or (lang p) ...)]
    ;; sequencing
    [((~or begin begin0) p) #'(lang p)] ;optimization
    [(begin0 p0 p ...)      #'(p-first (lang p0) (lang p) ...)]
    [(begin p0 p ...)       #'(p-last (lang p0) (lang p) ...)]
    ;; literals.
    [(~or x:boolean x:str x:char x:number) #'(p-eps x)]
    ;; function application. TODO: let-syntax.
    [(f:id p ...)   #'(p-map f (lang p) ...)]
    [(p ... --> f)  #'(p-map f (lang p) ...)]
    ;; escape hatch
    [(escape e)     #'e]))

(define-syntax-rule (fix/delay name body ...)
  (letrec ([name (delay body ...)]) name))

(define-syntax-rule (define-rule name clauses ...)
  (define name (fix/delay name body (lang (or clauses ...)))))


;; =============== Fixpoints & memoization ===============

(require racket/splicing)

;; The evaluation strategy here could be smarter. This re-runs *every* node
;; until all nodes in the computation "settle". But some nodes may settle early!
;; So some sort of dirty/clean marking strategy might give benefits.
;;
;; But you know what they say about premature optimization...

(define-syntax-rule (define/fix (f x) #:bottom bottom body ...)
  (splicing-let ([cache     (make-weak-hasheq)]
                 [changed?  (make-parameter 'error-changed)])
   (define (f x)
     (define (compute-fixpoint)
       (define visited (mutable-seteq))
       ;; note: is *deliberately* named same thing as outer function. this is
       ;; critical for recursive calls in (body ...) to work correctly.
       (define (f x)
         (define cached (hash-ref cache x (lambda () bottom)))
         ;; if we've already visited this node, give cached value
         (if (set-add?! visited x) cached
             ;; this is where we actually run the user-supplied code for the
             ;; fix-point computation.
             (let ([new-val (begin body ...)])
               (unless (equal? new-val cached)
                 (changed? #t)
                 (hash-set! cache x new-val))
               new-val)))
       (f x))
     (hash-ref! cache x compute-fixpoint))))

;; ;; A more HOF-flavored version:
;;
;; (define (fixify bottom meta-func)
;;   (define cache     (make-weak-hasheq))
;;   (define changed?  (make-parameter 'error-changed))
;;   (define (compute-fixpoint argument)
;;     (define visited (mutable-seteq))
;;     (define (visit node)
;;       (define cached (hash-ref cache node (lambda () bottom)))
;;       ;; if we've already visited this node, give cached value
;;       (if (set-add?! visited node) cached
;;           ;; this is where we actually run the user-supplied code for the
;;           ;; fix-point computation.
;;           (let ([new-val (inner node)])
;;             (unless (equal? new-val cached)
;;               (changed? #t)
;;               (hash-set! cache node new-val))
;;             new-val)))
;;     (define inner (meta-func visit))
;;     (visit argument))
;;   (lambda (x) (hash-ref! cache x (lambda () (compute-fixpoint x)))))
;;
;; (define-syntax-rule (define/fix- (f x) #:bottom bottom body ...)
;;   (define f (fixify bottom (lambda (f) (lambda (x) body ...)))))


;; =============== Core parsing code ===============
(define/fix (nullable? p)
  #:bottom #f
  (match (force p)
    [(p-eps* s)     (not (set-empty? s))]
    [(p-lit l)      (null? l)]
    [(p-one-of ps)  (ormap nullable? ps)]
    [(p-apply _ ps) (andmap nullable? ps)]))

(define/fix (parse-null p)
  #:bottom (set)
  (match (force p)
    [(p-eps* s) s]
    [(p-lit '()) (set '())]
    [(p-lit _) (set)]
    [(p-one-of ps) (set-unions (map parse-null ps))]
    [(p-apply f ps) (sets-map f (map parse-null ps))]))

;; should also do compaction
(define (p-derive p tok) TODO)


;; =============== Reverse parsing ===============
;; That is: generating strings from parsers!
(struct trie (null-parses out-parses) #:transparent)


;; =============== Test cases ===============
