#lang racket

(require "util.rkt") ;; TODO?: stop using this

;; ==================== Utilities ====================

(define debug? (make-parameter #f))
(define-syntax-rule (debug body ...) (when (debug?) body ...))

;; delay/force are cool. what's even cooler is forcing delayed thunks by
;; pattern-matching on them.
(require (rename-in racket/promise [delay real-delay]))
(define-match-expander delay
  (syntax-parser [(_ p)      #'(? promise? (app force p))])
  (syntax-parser [(_ e:expr) #'(real-delay e)]))

;; Some simple contracts
(define non-empty-set? (and/c set? (not/c set-empty?)))
(define non-empty-list? (non-empty-listof any/c))

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
       (sets-union
        (for/list ([elem s])
          (loop sets (cons elem acc))))])))

;; This maps a function `f' across the cartesian product of a list of sets,
;; producing a set of results.
;; `f' must accept N arguments, where N is the number of sets.
(define/contract (sets-map f sets)
  (-> procedure? (listof set?) set?)
  (for/set ([x (sets-product sets)])
    (apply f x)))


;; =============== Grammar & parser constructions ===============
;; NB. empty-parser? doesn't actually determine whether a parser is semantically
;; empty; it's just a shallow shape check.
(define grammar?          (hash/c symbol? (eta parser?) #:immutable #t))
(define empty-parser?     (eta (match/c (p/union '()))))
(define non-empty-parser? (eta (and/c parser? (not/c empty-parser?))))
(define non-union-parser? (eta (and/c parser? (not/c (eta p/union?)))))

(enum parser
  (p/named  name)
  (p/tok    token)
  (p/pure   [results non-empty-set?])
  (p/union  [parsers (and/c (listof non-union-parser?)
                            (not/c (list/c parser?)))])
  (p/apply  func [parsers (non-empty-listof non-empty-parser?)]))

;; the empty parser is (p/union '())
;; the null parser is  (p/pure _)

;; smart constructors, which perform some simplifications (but not complete
;; compaction) on-the-fly.
(define p-named p/named)
(define p-tok   p/tok)
(define p-empty (p/union '()))

(define (p-pure s)
  (if (set-empty? s) p-empty (p/pure s)))

(define (p-union ps)
  ;; flattens nested p-unions, which also drops unnecessary p-emptys.
  (define/match (parser->list p)
    [((p/union l)) l]
    [(x) (list x)])
  (match (append-map parser->list ps)
    ;; a union of one thing is just that thing.
    [(list p) p]
    [ps (p/union ps)]))

(define (p-apply f parsers)
  (match parsers
    ;; if any argument is empty, we are empty
    [(list _ ... (? empty-parser?) _ ...) p-empty]
    ;; if all arguments are provided, call the function
    [(list (p/pure sets) ...) (p-pure (sets-map f sets))]
    ;; function composition
    [(list (p/apply g ps)) (p/apply (compose f g) ps)]
    [_ (p/apply f parsers)]))

;; convenient parser combinators.
(define (p-eps x) (p-pure (set x)))
(define (p-or . ps) (p-union ps))
(define (p-map f . parsers) (p-apply f parsers))

(define (p-first p . ps) (p-apply first (cons p ps)))
(define (p-last p . ps) (p-apply last (cons p ps)))
(define (p-list . ps) (p-apply list ps))


;; =============== Dealing with variables ===============
(define (free-vars p)
  (match p
    [(p/named name)                     (set name)]
    [(or (p/pure _) (p/tok _))          (set)]
    [(or (p/union ps) (p/apply _ ps))   (sets-union (map free-vars ps))]))


;; =============== Syntax sugar ===============

;; TODO: allow name to be used multiple times to create multiple clauses which
;; are implicitly unioned.
(define-syntax-parser (grammar [name body ...] ...)
  #'(let ([name (p-named 'name)] ...)
      (make-immutable-hash `((name . ,(lang body ...)) ...))))

(define-syntax-rule (define-grammar name clauses ...)
  (define name (grammar clauses ...)))

(define-syntax-parser lang
  [(_ e)     (lang-parse #'e)]
  [(_ e ...) (lang-parse #'(begin e ...))])

;; TODO: letrec syntax. binding syntax. "x:expr" syntax? "==>" syntax?
(define-for-syntax lang-parse
  (syntax-parser
    #:datum-literals (pure eps quote ? empty fix escape -->)
    #:literals (begin0 begin or)
    [((~or eps pure) v ...) #'(p-pure (set v ...))]
    [(~or x:boolean x:str x:char x:number) #'(p-eps x)]
    [(quote x)              #'(p-tok 'x)]
    ;; alternation
    [empty                  #'p-empty]
    [(or p ...)             #'(p-or (lang p) ...)]
    ;; sequencing
    [((~or begin begin0) p) #'(lang p)] ;optimization
    [(begin0 p0 p ...)      #'(p-first (lang p0) (lang p) ...)]
    [(begin p0 p ...)       #'(p-last (lang p0) (lang p) ...)]
    ;; function application.
    [(f:id p ...)           #'(p-map f (lang p) ...)]
    [(p ... --> f)          #'(p-map f (lang p) ...)]
    ;; getting back to reality
    [e:id                   #'e]        ;has to go below #'empty case.
    [(escape e)             #'e]))


;; =============== Iteratively computing fixed points ===============
(define (fixpoint func #:init init #:equal [equalp equal?])
  (let loop ([prev init])
    (define next (func prev))
    (if (equalp prev next) prev
        (loop next))))

(define-syntax-rule (let/fix [name init] body ...)
  (fixpoint (lambda (name) body ...) #:init init))


;; =============== Core parsing code ===============

(require racket/splicing)

(define-syntax-parser (define/flow (name parser-param)
                        #:init init
                        body ...)
  #`(define (#,(format-id "grammar-~a" #'name) G)
      (let/fix [memo (hash-map-vals (const init) G)]
        (define/match (name parser-param)
          [((p/named name)) (hash-ref memo name)]
          [(_) body ...])
        (hash-map-vals name G))))

;; (define/flow (nullable p)
;;   #:init #f
;;   (match p
;;     [(p/tok _)      #f]
;;     [(p/pure _)     #t]
;;     [(p/union ps)   (ormap nullable ps)]
;;     [(p/apply f ps) (andmap nullable ps)]))

(define/flow (is-empty p)
  #:init #t
  (match p
    [(p/tok _)      #f]
    [(p/pure _)     #f]
    [(p/union ps)   (andmap is-empty ps)]
    [(p/apply f ps) (ormap  is-empty ps)]))

(define/flow (parse-null p)
  #:init (set)
  (match p
    [(p/tok _)      (set)]
    [(p/pure s)     s]
    [(p/union ps)   (sets-union (map parse-null ps))]
    [(p/apply f ps) (sets-map f (map parse-null ps))]))

;; To implement: Inlining parsers that are only referenced once; inlining
;; parsers which immediately refer to another parser.
;;
;; Should separate compaction from pruning. Pruning involves a chosen set of
;; "root references" (helloooo garbage collection), which can't be pruned.
;; Compaction doesn't.
(define (compact G)
  (define G-empty      (grammar-is-empty G))
  ;; compacts a parser, which amounts to pushing empties through.
  (define (local-compact p)
    (match p
      [(p/named n) #:when (hash-ref G-empty n)  p-empty]
      [(or (p/named _) (p/tok _) (p/pure _))    p]
      [(p/union ps)     (p-union (map local-compact ps))]
      [(p/apply f ps)   (p-apply f (map local-compact ps))]))
  (hash-map-vals local-compact G))

;; To implement: pruning unreachable parsers.
(define (prune G #:roots roots) TODO)

(define (derive c G)
  (define G-nulls (grammar-parse-null G))
  (define deriv-names (for/hash ([name (hash-keys G)])
                        (values name (gensym (format "d_~a" name)))))
  (define (local-derive p)
    (match p
      [(p/named n)      (p/named (hash-ref deriv-names n))]
      [(p/tok (== c))   (p/pure (set c))]
      [(p/tok _)        p-empty]
      [(p/pure _)       p-empty]
      [(p/union ps)     (p-union (map local-derive ps))]
      ;; the fun case
      [(p/apply f ps)
       ;; FIXME aaslkdjflksdjfljsadjfasdf this doesn't work.
       ;; it's fixable in principle.
       (define nulls  (map (curry hash-ref G-nulls) ps)) ;WRONG WRONG WRONG
       (define derivs (map local-derive ps))
       (p-union
        (for/list ([i (length ps)])
          (define head (take nulls i))
          (define tail (drop ps (+ 1 i)))
          (p-apply f (append (map p-pure head)
                             (list (list-ref derivs i))
                             tail))))]))
  (define derivs
    (for/hash ([(name deriv-name) deriv-names])
      (values deriv-name (local-derive (hash-ref G name)))))
  (hash-union-right G derivs))


;; =============== Examples ===============
(define-grammar test
  [nil      empty]
  [self     self]
  [eps      (pure 'hello)]
  [hello    (list 'hello 'world)]
  [nat      (or (list 'z) (cons 's nat))]
  [zs       (or (list)    (cons 'z zs))])

(define-grammar num
  [digit (or '0 '1 '2 '3 '4 '5 '6 '7 '8 '9)]
  [num   (+ (* 10 num) digit)])

(define-syntax-rule (? e) (syntax->datum (expand-once #'e)))
