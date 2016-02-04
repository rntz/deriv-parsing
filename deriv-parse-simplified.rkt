#lang racket

;; this is an experiment. it's not clear it simplifies anything yet, or is even
;; feasible.

;; ==================== Utilities ====================

;; makes a hash from a sequence of keys and a function that turns keys into
;; values.
(define (tabulate keys f)
  (for/hash ([k keys]) (values k (f k))))

;; maps a function across a hash's values, returning new hash.
(define (hash-map-vals f h)
  (for/hash ([(k v) h]) (values k (f v))))

;; takes the union of two hashes, using `f' to combine values where both keys
;; are present.
(define (hash-union-with f h1 h2)
  (tabulate (set-union (list->set (hash-keys h1)) (list->set (hash-keys h2)))
            (lambda (k) (match* ((hash-has-key? h1 k) (hash-has-key? h2 k))
                     [(#t _) (hash-ref h1 k)]
                     [(_ #t) (hash-ref h2 k)]
                     [(#t #t) (f (hash-ref h1 k) (hash-ref h2 k))]))))

;; takes the union of an arbitrary number of hashes, using `f' to combine values
;; at all keys. `f' is called with a list of the values a key is mapped to (in
;; each hash in which it is present at all).
(define (hash-unions-with f hashes)
  (tabulate (sets-union (map (compose list->set hash-keys) hashes))
            (lambda (k)
              (f (for/list ([h hashes]
                            #:when (hash-has-key? h k))
                   (hash-ref h k))))))

;; takes the union of a (possibly empty) list of sets
(define (sets-union sets) (apply set-union (set) sets))

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
(define (sets-map f sets)
  (for/set ([x (sets-product sets)])
    (apply f x)))

;; n-ary version of sets-map
(define (set-map* f . sets) (sets-map f sets))


;; ==================== Parser structures & types ====================

;; A non-empty parser is represented by a structure with `null-parses' and
;; `derivative' fields.
;;
;; `null-parses' is a set of our null parses.
;;
;; `derivative' is a promise that generates a hash mapping from tokens to our
;; derivative under those tokens.
;;
;; all laziness comes from the fact that `derivative' is a promise.
(struct parser-nonempty (null-parses derivative) #:transparent)

;; The empty parser is represented by #f.
(define (parser-empty? x) (not x))
(define parser? (or/c #f parser-nonempty?))

;; Because of how we define parsers, the operations that require fixpoints &
;; memoization in "Parsing with Derivatives" are trivial for us. However, see
;; "Constructing parsers", below.
(define (null-parses x)
  (if x (parser-nonempty-null-parses x) (set)))
(define (nullable? x)
  (not (set-empty? (null-parses x))))
(define (derivative p)
  (if p (force (parser-nonempty-derivative p)) (hash)))
(define (p-deriv p c)
  (hash-ref (derivative p) c #f))


;; ==================== Running parsers ====================
(define (parse p toks)
  (match toks
    ['() (null-parses p)]
    [(cons c toks) (parse (p-deriv p c) toks)]))


;; ==================== Constructing parsers ====================

;; However, in "Parsing with Derivatives", constructing parsers is trivial:
;; they're just branches of a datatype! This is harder for us, since our parsers
;; have computational content.

(define (p-eps* x-set)
  (and (not (set-empty? x-set))
       (parser-nonempty x-set (const (hash)))))

;; The \delta combinator from the paper. Produces only the null parses of a
;; given parser.
(define (p-null p) (p-eps* (null-parses p)))

(define (p-tok tok) (parser-nonempty (set) (hash tok (p-eps tok))))

;; ;; NB. p-class could technically be empty if `pred' is (const #f).
;; (define (p-tok tok) (p-class (lambda (c) (equal? c tok))))
;; (define (p-class pred)
;;   (parser-nonempty (set)
;;                    (lambda (c) (and (pred c) (p-eps c)))))

;; parser union and its identity, the empty parser
(define p-empty #f)
(define (p-or . ps) (p-one-of ps))
(define (p-one-of ps)
  (match (filter identity ps)
    ;; if there are none, we're empty:
    ['() #f]
    ;; if there's exactly one, we just return it:
    [(list p) p]
    ;; the general case:
    [(list (parser-nonempty null-parses derivs) ...)
     (parser-nonempty
      (apply set-union null-parses)
      (delay (hash-unions-with p-one-of (map force derivs))))]))

;; Haskell programmers and Parsec users would call p-eps "return" or "pure".
;; the variadic p-map shows that parsers are a monoidal/applicative functor.
(define (p-eps x) (p-eps* (set x)))
;;; problem: laziness
(define (p-map f . ps)
  (and (andmap parser-nonempty? ps)
       (match ps
         ['() (p-eps (f))]
         [(list (parser-nonempty null-parses deriv))
          (parser-nonempty
           (for/set ([x null-parses]) (f x))
           (delay (hash-map-vals (lambda (x) (p-map f x)) (force deriv))))]
         ;; the general case uses the 1-argument case and p-cons.
         [_ (p-map (curry apply f)
                   (foldr p-cons (p-eps '()) ps))])))

(define (p-cons p0 p1)
  (and p0 p1
       (parser-nonempty
        (set-map* cons (null-parses p0) (null-parses p1))
        (delay
          (define d0 (derivative p0))
          (define d1 (derivative p1))
          (hash-union-with
           p-or
           (hash-map-vals (lambda (p) (p-cons p p1)) d0)
           (hash-map-vals (lambda (p) (p-cons (p-null p0) p)) d1))))))

(define (p-list . ps) (apply p-map list ps))
(define (p-first p . ps) (apply p-map (lambda (x . a) x) p ps))
(define (p-last p . ps) (apply p-map (lambda a (last a)) p ps))

;; Iteration of a parser. An example of a recursive parser constructed manually,
;; rather than using the fixed-point stuff below.
(define (p-iter p)
  (when (nullable? p) (error "cannot iterate a nullable parser"))
  (define deriv
    (delay (hash-map-vals (lambda (x) (p-cons x (p-iter p))) (derivative p))))
  (and p (parser-nonempty (set '()) deriv)))


;; ==================== Recursive parsers ====================

;; The hardest thing for us, of course, is constructing *recursive* parsers.
;; Here's where the heavy-duty memoized-least-fix-point weaponry comes out.

(require racket/splicing (for-syntax syntax/parse))

(define-syntax define-recursive-parser
  (syntax-parser
    ;; TODO: recursive parsers with parameters
    [(_ name:id body ...) #'(define name (recursive-parser name body ...))]))

(define-syntax-rule (recursive-parser name body ...)
  (let ()
    (define (iter name) body ...)
    (match (iter #f)
      ;; if #f will satisfy, then #f is the result.
      [#f #f]
      ;; otherwise, we perform a clever trick...
      [(parser-nonempty init-null-parses init-deriv)
       ;; first, we compute the null parses using a least-fixed point. the
       ;; derivative should not be used during this computation, so it's safe to
       ;; set it to some garbage value.
       (define null-parses
         (let loop ([nulls init-null-parses])
           (printf "looping: ~a\n" nulls)
           (match (iter (parser-nonempty nulls 'garbage))
             [#f (error "non-monotonic recursive parser!")]
             [(parser-nonempty new-nulls _)
              (if (equal? nulls new-nulls)
                  nulls
                  (loop new-nulls))])))
       ;; next, we make a derivative function using the classic "swap it in
       ;; later" trick for defining recursive functions.
       (define deriv 'error)
       (define deriv-delayed (delay deriv))
       (define result (iter (parser-nonempty null-parses deriv-delayed)))
       (when (promise-forced? deriv-delayed)
         (error "fuck, forced promise too soon"))
       (printf "forcing result...\n")
       ;; welp, here's the bug
       (set! deriv (derivative result))
       (printf "WORKED!: ~a\n" deriv)
       result])))


;; ==================== Syntax sugar for parsers ====================

(require (for-syntax syntax/parse))

(define-syntax lang
  (syntax-parser
    [(_ e) (lang-parse #'e)]
    [(_ e ...) (lang-parse #'(begin e ...))]))

(define-for-syntax lang-parse
  (syntax-parser
    #:datum-literals (eps pure quote ? empty escape -->)
    #:literals (begin0 begin or cons let)
    [e:id #'e]
    [((~or eps pure) v ...) #'(p-eps* (set v ...))]
    ;; TODO: maybe quote should be used for tokens?
    ;; and '? should be used for class? dunno.
    [(quote x)          #'(p-tok 'x)]
    ;; [(? pred)           #'(p-class pred)]
    ;; alternation
    [empty          #'p-empty]
    [(or p ...)     #'(p-or (lang p) ...)]
    ;; sequencing
    [((~or begin begin0) p) #'(lang p)] ;optimization
    [(begin0 p0 p ...)      #'(p-first (lang p0) (lang p) ...)]
    [(begin p0 p ...)       #'(p-last (lang p0) (lang p) ...)]
    ;; literals.
    [(~or x:boolean x:str x:char x:number) #'(p-eps x)]
    ;; function application
    [(cons a b)     #'(p-cons (lang a) (lang b))] ;optimization
    [(f:id p ...)   #'(p-map f (lang p) ...)]
    [(p ... --> f)  #'(p-map f (lang p) ...)]
    ;; escape hatch
    [(escape e)     #'e]))

(define-syntax-rule (define-rule name clauses ...)
  (define name (recursive-parser name (lang (or clauses ...)))))


;; ==================== Examples ====================
(define hello (p-tok 'hello))
(define hellos (p-iter hello))
(define allo-allo (lang (cons hellos hellos)))

(define foo (recursive-parser foo (lang (or 'foo (cons 'bar 'baz)))))

(define-recursive-parser nat (lang (or 'z (list 's nat))))

;; (define-rule expr
;;   (? number?)
;;   'foo
;;   ;; (expr '+ expr)
;;   )

(define-syntax-rule (? e) (syntax->datum (expand-once #'e)))


;; ==================== Open problems ====================

;; Open problem: how to handle "open recursion"?
;;
;; that is, to define a recursive parser P which can later be extended:
;;
;;   P' ::= [P'/P] P | [P'/P] E
;;
;; where, by a slight abuse of substitution notation, what I mean to convey is
;; that in the "extended" parser P', recursive references to P in P's definition
;; (and in E's) are taken instead to refer to P'. by way of example, consider:
;;
;;   e ::= e + e | e * e
;;
;; Note that `e' is an empty parser here, as it is without a base case. However,
;; if we *extend* it with the following:
;;
;;   e ::= 0 | 1 | ...
;;
;; this yields a combined grammar:
;;
;;   e ::= e + e | e * e
;;       | 0 | 1 | ...
;;
;; in other words, we obtain a grammar for arithmetic!
