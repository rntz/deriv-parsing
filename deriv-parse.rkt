#lang racket

;; This is my reimplementation of derivative parsing in Racket.

(require "util.rkt")
(require "immutable-queue.rkt")
(require "iterative-deepening.rkt")

;; ==================== Utilities ====================

;; TODO: remove this in favor of Racket's standard logging stuff?
(define debug? (make-parameter #f))
(define-syntax-rule (debug body ...) (when (debug?) body ...))

;; delay/force are cool. what's even cooler is forcing delayed thunks by
;; pattern-matching on them. this makes pattern-matching side-effectful,
;; however, so use with care.
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
  (for/fold ([tuples (set '())])
            ([s (reverse sets)])
    (for*/set ([x s] [xs tuples])
      (cons x xs))))

;; This maps a function `f' across the cartesian product of a list of sets,
;; producing a set of results.
;; `f' must accept N arguments, where N is the number of sets.
(define/contract (sets-map f sets)
  (-> procedure? (listof set?) set?)
  (for/set ([x (sets-product sets)])
    (apply f x)))


;; =============== Parser structures & constructors ===============

;; A parser is either:
;; - a promise returning a parser, or
;; - a concrete parser (see below)
(define parser? (or/c promise? (eta concrete-parser?)))

;; NB. empty-parser? doesn't actually determine whether a parser is semantically
;; empty; it's just a shallow shape check.
(define empty-parser?     (match/c (p/union '())))
(define non-empty-parser? (and/c parser? (not/c empty-parser?)))
(define non-union-parser? (and/c parser? (not/c (eta p/union?))))

(enum concrete-parser
  (p/tok    token)
  (p/pure   [results non-empty-set?])
  (p/union  [parsers (and/c (listof non-union-parser?)
                            (not/c (list/c parser?)))])
  ;; (p/map  func [parser non-empty-parser?])
  ;; (p/cons [a non-empty-parser?] [b non-empty-parser?])
  (p/apply  func [parsers (non-empty-listof non-empty-parser?)]))

;; the empty parser is (p/union '())
;; the null parser is  (p/pure _)
;;
;; TODO: have explicit empty parser? and tighten constraint on p/union's
;; arguments?

;; smart constructors, which perform some simplifications (but not complete
;; compaction) on-the-fly.
(define p-tok p/tok)
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

(define/contract (p-apply f parsers)
  (-> procedure? (listof parser?) parser?)
  (match parsers
    ;; if any argument is empty, we are empty
    [(list _ ... (? empty-parser?) _ ...) p-empty]
    ;; if all arguments are provided, call the function
    [(list (p/pure sets) ...) (p-pure (sets-map f sets))]
    ;; function composition.
    ;; how necessary/useful is this "optimization"?
    [(list (p/apply g ps)) (p/apply (compose f g) ps)]
    [_ (p/apply f parsers)]))

;; convenient parser combinators.
(define (p-eps x) (p-pure (set x)))
(define (p-or . ps) (p-union ps))
(define (p-map f . parsers) (p-apply f parsers))

(define (p-first p . ps) (p-apply first (cons p ps)))
(define (p-last p . ps) (p-apply last (cons p ps)))
(define (p-list . ps) (p-apply list ps))


;; =============== Syntax sugar ===============
(require (for-syntax syntax/parse))

(define-syntax lang
  (syntax-parser
    [(_ e) (lang-parse #'e)]
    [(_ e ...) (lang-parse #'(begin e ...))]))

;; TODO: let-syntax. x:expr syntax? ==> syntax?
(define-for-syntax lang-parse
  (syntax-parser
    #:datum-literals (pure eps quote ? empty fix escape -->)
    #:literals (begin0 begin or)
    [e:id                   #'e]
    ;; recursive parsers. see fix/delay, below.
    [(fix name p ...)       #'(fix/delay name (lang (or p  ...)))]
    ;; literals/pure
    [((~or eps pure) v ...) #'(p-pure (set v ...))]
    [(~or x:boolean x:str x:char x:number) #'(p-eps x)]
    ;; tokens
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
    ;; escape hatch
    [(escape e)             #'e]))

(define-syntax-rule (fix/delay name body ...)
  (letrec ([name (delay body ...)]) name))

(define-syntax-rule (define-rule name clauses ...)
  (define name (lang (fix name clauses ...))))


;; =============== Fixpoints & memoization ===============

(require racket/splicing)

;;; TODO FIXME: there's some bug involving user breaks during a call to a
;;; memoized or fix-point function, that causes the exception to get re-raised
;;; or something.

;; why is it "define/memo!", you ask, and not simply "define/memo"?
;; because it has a side effect! for example,
;;
;;     (define/memo! (foo x) ...)
;;     (define (bar x) (foo x))
;;
;; is NOT the same as:
;;
;;     (define (bar x)
;;       (define/memo! (foo x) ...)
;;       (foo x))
;;
;; The case of define/memo that implements multi-argument memoization via
;; currying used to have a bug caused by this very difference!
(define-syntax-parser define/memo!
  [(_ (f x) body ...)
   #'(splicing-let ([memo-table (make-weak-hasheq)]
                    [computing  (make-parameter (set))])
       (define (f x)
         (define (compute)
           (debug (printf "computing: (~a ~v)\n" 'f x))
           (when (set-member? (computing) x)
             (error "recursive call to memoized function"))
           (parameterize ([computing (set-add (computing) x)])
             body ...))
         (debug
          (when (hash-has-key? memo-table x)
            (printf "cached:    (~a ~v) = ~v\n" 'f x (hash-ref memo-table x))))
         (hash-ref! memo-table x compute)))]

  ;; for 2 or more arguments, we use a (simple trick / awful hack): currying!
  [(_ (f x y ...) body ...)
   #'(begin
       (define/memo! (outer x)
         (define/memo! (inner y ...) body ...)
         inner)
       (define (f x y ...)
         ((outer x) y ...)))])

;; The evaluation strategy here could be smarter. This re-runs *every* node
;; until all nodes in the computation "settle". But some nodes may settle early!
;; So some sort of dirty/clean marking strategy might give benefits.
;;
;; But you know what they say about premature optimization...

(define-syntax-rule (define/fix (f x) #:bottom bottom body ...)
  (splicing-let ([cache     (make-weak-hasheq)]
                 ;; FIXME: what is this used for?
                 [changed?  (make-parameter 'error-changed)])
   (define (f x)
     ;; TODO: hoist this out of f.
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
       (let loop ()
         (parameterize ([changed? #f])
           (define result (f x))
           (if (changed?) (loop) result))))
     (hash-ref! cache x compute-fixpoint))))


;; =============== Core parsing code ===============
(define/fix (nullable? p)
  #:bottom #f
  (match p
    [(delay p)      (nullable? p)]
    [(p/tok t)      #f]
    [(p/pure s)     #t]
    [(p/union ps)   (ormap nullable? ps)]
    [(p/apply _ ps) (andmap nullable? ps)]))

(define/fix (parse-null p)
  #:bottom (set)
  (match p
    [(delay p)      (parse-null p)]
    [(p/pure s)     s]
    [(p/tok _)      (set)]
    [(p/union ps)   (sets-union (map parse-null ps))]
    [(p/apply f ps) (sets-map f (map parse-null ps))]))

(define/fix (is-empty? p)
  #:bottom #t
  (match p
    [(delay p)      (is-empty? p)]
    [(p/pure _)     #f]
    [(p/tok _)      #f]
    [(p/union ps)   (andmap is-empty? ps)]
    [(p/apply f ps) (ormap is-empty? ps)]))

;; uses is-empty?
;;
;; TODO: double check that this implements all the compactions in the new
;; derivative parsing paper, the one with the proof of O(n^3) worst-case
;; performance.
(define/memo! (compact p)
  (match p
    [(? is-empty?)      p-empty]
    ;; TODO: is this right? explain why it's okay not to force here. maybe
    ;; it's because we already called is-empty?
    [(? promise?)       (delay (compact (force p)))]
    [(p/pure _)         p]
    [(p/tok _)          p]
    ;; Our smart constructors do most of the work for us.
    [(p/union ps)       (p-union (map compact ps))]
    [(p/apply f ps)     (p-apply f (map compact ps))]))

(define/memo! (derive c p)
  (match p
    ;; this delay is critical to avoid infinite looping.
    ;; WHY? what's an example?
    [(? promise?)   (delay (derive c (force p)))]
    [(p/pure _)     p-empty]
    [(p/tok (== c)) (p-eps c)]
    [(p/tok _)      p-empty]
    [(p/union ps)   (p-union (map (curry derive c) ps))]
    [(p/apply f ps)
     (define nulls  (map parse-null       ps))
     (define derivs (map (curry derive c) ps))
     (p-union
      ;; NB. could be more efficient about noticing empty null-sets here.
      (for/list ([i (length ps)])
        (define head (take nulls i))
        (define tail (drop ps (+ 1 i)))
        (p-apply f (append (map p-pure head)
                           (list (list-ref derivs i))
                           tail))))]))

;; finds the set of tokens which lead to non-empty derivatives.
(define/fix (next-tokens p)
  #:bottom (set)
  (match p
    [(delay p)      (next-tokens p)]
    [(p/pure _)     (set)]
    [(p/tok t)      (set t)]
    [(p/union ps)   (sets-union (map next-tokens ps))]
    [(p/apply f ps)
     ;; find all nullable prefixes of ps.
     (define-values (head tail) (splitf-at ps nullable?))
     (define nexts (if (null? tail) head (cons (car tail) head)))
     (sets-union (map next-tokens nexts))]))


;; =============== Running parsers ===============
(define (parse p toks) (parse-null (derive* toks p)))
(define (derive* toks p)
  (for/fold ([p p]) ([tok toks])
    (derive tok (compact p))))

(define (derive-hash p)
  (for/hash ([c (next-tokens p)])
    (values c (derive c p))))


;; =============== Reverse parsing ===============
;; That is: generating strings from parsers!

;; A trie's `parses' is a set of its null parses.
;; A trie's `children' is a hash from tokens to promises that deliver tries.
(struct trie (parses children) #:transparent)

(define (parser->trie p)
  (set! p (compact p))
  (trie (parse-null p)
        (for/hash ([(tok next) (derive-hash p)])
          (values tok (delay (parser->trie next))))))

;; forces a trie to the given depth.
;; #f means "force it all the way".
;; pun unintentional, I swear. really! you don't believe me?!
(define (trie-force t #:depth [depth #f])
  (match depth
    [0 t]
    [_
     (match-define (trie parses children) (force t))
     (trie parses
           (for/hash ([(tok next) children])
             (values tok
                     (trie-force next #:depth (and depth (- depth 1))))))]))
;;
;; uses iterated deepening to avoid problems with asymptotically huge space
;; usage, while imposing only an asymptotically negligible time overhead.
;; TODO: be more precise about the asymptotics.
;;
;; TODO: construct an example where /not/ using iterated deepening produces
;; memory issues.
;;
;; FIXME: (stream->list (all-parses digit)) infloops
;; (define (all-parses p)
;;   (define (deepen n p rev-toks)
;;     (set! p (compact p))
;;     (match n
;;       [0 (define parses (parse-null p))
;;          (if (set-empty? parses) '()
;;              (list (list (reverse rev-toks) parses)))]
;;       [_ (let*/stream ([(tok next-p) (derive-hash p)])
;;            (deepen (- n 1) next-p (cons tok rev-toks)))]))
;;   ;; HERP, this doesn't know when to stop deepening!
;;   (let*/stream ([n (in-naturals)])
;;     (deepen n p '())))

;; produces a lazy tree of (token-list set-of-parses) values.
;;
;; TODO: are there optimizations I can apply here? to avoid empty internal
;; nodes, for example?
(define (parser->lazytree parser)
  (let parser->lazytree ([p parser] [rev-toks '()])
    (set! p (compact p))
    (define parses (parse-null p))
    (lazytree
     (list (list (reverse rev-toks) parses))
     (for/list ([(tok next-p) (derive-hash p)])
       (parser->lazytree next-p (cons tok rev-toks))))))

(define (in-parses parser)
  (sequence-filter
   (match-lambda [(list toks parse-set) (not (set-empty? parse-set))])
   (in-lazytree (parser->lazytree parser))))

(define (in-grammar parser) (sequence-map first (in-parses parser)))
(define (all-terms p) (sequence->stream (in-grammar p)))
(define (all-parses p) (sequence->stream (in-parses p)))

;; old version. would be cool if this could be defined as:
;; (define (all-parses p) (trie->stream (parser->trie p)))

;; generates a stream of (token-list set-of-parses) elements.
;;
;; TODO: Can this ever fail to create a productive stream? I think it probably
;; can, but only if the grammar is unproductive. Even then, compaction and
;; empty-testing probably save us often. But it seems unlikely they can always
;; save us.
(define (all-parses-old p)
  (let work ([q (list->queue (list (list p '())))])
    (if (queue-empty? q) empty-stream
        (let-values ([(q x) (dequeue q)])
          (match-define (list p rev-toks) x)
          (set! p (compact p))
          (define parses (parse-null p))
          ;; push successors onto the queue
          (set! q (for/fold ([q q])
                            ([(tok p-next) (derive-hash p)])
                    (enqueue q `(,p-next (,tok ,@rev-toks)))))
          (if (set-empty? parses)
              (work q)
              (stream-cons `(,(reverse rev-toks) ,parses) (work q)))))))


;; =============== Test cases ===============
(define-rule self self)
(define-rule infsum infsum infsum)
(define-rule inflist (list inflist inflist))

;; FIXME: (all-parses nat) does not work
(define-rule nat 'z (list 's nat))
(define-rule zs (eps '()) (cons 'z zs))

(define-rule digit '0 '1 '2 '3 '4 '5 '6 '7 '8 '9)

(define-rule expr
  digit
  (list expr '+ expr)
  (list expr '* expr))

(define (generate n-examples parser)
  (map car (stream-take n-examples (all-parses parser))))

(module+ test
  (println (stream->list (all-parses digit)))

  ;; TODO: test submodule with actual tests!
  (println (parse nat '(z)))
  (println (parse nat '(s s z)))

  (println (stream-take 4 (all-parses nat)))
  )
