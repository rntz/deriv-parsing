#lang racket

;; This is my reimplementation of derivative parsing in Racket, in which I try
;; to be super-explicit about use of recursion in parsers.

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


;; =============== Parser structures & constructors ===============

;; NB. empty-parser? doesn't actually determine whether a parser is semantically
;; empty; it's just a shallow shape check.
(define empty-parser?     (eta (match/c (p/union '()))))
(define non-empty-parser? (eta (and/c parser? (not/c empty-parser?))))
(define non-union-parser? (eta (and/c parser? (not/c (eta p/union?)))))

(enum parser
  ;; a recursive parser, whose contents may refer to themselves using `name'.
  (p/rec    name [contents parser?])
  ;; refers to a name bound by a p/rec.
  (p/var    name)
  (p/tok    token)
  (p/pure   [results non-empty-set?])
  (p/union  [parsers (and/c (listof non-union-parser?)
                            (not/c (list/c parser?)))])
  (p/apply  func [parsers (non-empty-listof non-empty-parser?)]))

;; the empty parser is (p/union '())
;; the null parser is  (p/pure _)

;; smart constructors, which perform some simplifications (but not complete
;; compaction) on-the-fly.
(define p-var p/var)
(define p-tok p/tok)
(define p-empty (p/union '()))

(define (p-pure s)
  (if (set-empty? s) p-empty (p/pure s)))

(define (p-rec name contents)
  (if (empty-parser? contents) p-empty
      (p/rec name contents)))

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
    ;; recursive parsers.
    [(fix name p ...)       #'(let ([name (p-var 'name)])
                                (p-rec 'name (lang (or p  ...))))]
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

(define-syntax-rule (define-rule name clauses ...)
  (define name (lang (fix name clauses ...))))


;; =============== Dealing with variable binding ===============
(define (free-vars p)
  (match p
    [(p/rec name content)               (set-remove (free-vars content) name)]
    [(p/var name)                       (set name)]
    [(or (p/pure _) (p/tok _))          (set)]
    [(or (p/union ps) (p/apply _ ps))   (sets-union (map free-vars ps))]))

(define (substitute p var body)
  (match body
    [(p/var (== var))   p]
    [(or (p/var _) (p/pure _) (p/tok _)) body]
    [(p/union ps)       (p-union (map (curry substitute p var) ps))]
    [(p/apply f ps)     (p-apply f (map (curry substitute p var) ps))]
    [(p/rec name contents)
     ;; I *think* with the way I've set things up we should never end up needing
     ;; to alpha-vary.
     (assert! (not (equal? var name)))
     (p/rec name (substitute p var contents))]))


;; =============== Iteratively computing fixed points ===============
(define (fixpoint init func #:equal [equalp equal?])
  (let loop ([prev init])
    (define next (func prev))
    (if (equalp prev next) prev
        (loop next))))

(define-syntax-rule (let/fix [name init] body ...)
  (fixpoint init (lambda (name) body ...)))


;; =============== Core parsing code ===============
(define nullable-memo (make-parameter (hash)))
(define (nullable? p)
  (match p
    ;; NB. No need to use 'fixpoint here; there are only two possible values: #f
    ;; and #t. So we only need to iterate once!
    [(p/rec name contents)
     (parameterize ([nullable-memo (hash-set (nullable-memo) name #f)])
       (nullable? contents))]
    ;; Given the above, we *could* simply have (nullable? (p/var _)) return #f.
    ;; However, we ought only ever to call (nullable? (p/var name)) recursively
    ;; within a call to (nullable? (p/rec name _)); by doing it this way, we'll
    ;; get a runtime error if we mistakenly call (nullable? (p/var _)) directly.
    [(p/var name)   (hash-ref (nullable-memo) name)]
    [(p/tok t)      #f]
    [(p/pure s)     #t]
    [(p/union ps)   (ormap nullable? ps)]
    [(p/apply _ ps) (andmap nullable? ps)]))

(define is-empty-memo (make-parameter (hash)))
(define (is-empty? p)
  (match p
    ;; NB. As in nullable?, no need to use 'fixpoint here, because there are
    ;; only two possible values.
    [(p/rec name contents)
     (parameterize ([is-empty-memo (hash-set (is-empty-memo) name #t)])
       (is-empty? contents))]
    [(p/var name)   (hash-ref (is-empty-memo) name)]
    [(p/pure _)     #f]
    [(p/tok _)      #f]
    [(p/union ps)   (andmap is-empty? ps)]
    [(p/apply f ps) (ormap is-empty? ps)]))

(define parse-null-memo (make-parameter (hash)))
(define (parse-null p)
  (match p
    [(p/rec name contents)
     (let/fix [self (set)]
       (parameterize ([parse-null-memo (hash-set (parse-null-memo) name self)])
         (parse-null contents)))]
    [(p/var name)   (hash-ref (parse-null-memo) name)]
    [(p/pure s)     s]
    [(p/tok _)      (set)]
    [(p/union ps)   (sets-union (map parse-null ps))]
    [(p/apply f ps) (sets-map f (map parse-null ps))]))

;; The derivative of a recursive parser can refer /both/ to the original parser
;; and to its derivative, so things get a little hairy. In the recursive case:
;;
;; 1. We produce a recursive parser which refers to itself with a fresh
;;    name, `derive-name'.
;;
;; 2. We bind `name' to `deriv-name' in `derive-memo' when we recurse, so that
;;    the derivative of recursive refernces to `p' becomes (p/var deriv-name).
;;
;; 3. We substitute `p' for `name' in the result.
;;
;; Note that step 3 can duplicate `p' and lead to parser size blowup! There
;; are a few possible solutions to this:
;;
;; 1. Full-on memoization. this is probably the simplest solution, but it's
;;    part of what I was trying to avoid, for clarity's sake.
;;
;; 2. An explicit (p/let name p1 p2) form, which binds name to p1 in p2.
;;    This complicates things. It's possible explicit substitutions might be
;;    useful in addition or instead of this, but I'm not sure.
;;
;; 3. Represent parsers as graphs rather than trees, perhaps using an
;;    adjacency-list representation. This is effectively the memoization
;;    solution, but making the graph explicit instead of re-using the
;;    object-in-memory graph.
;;
;; 4. Represent full-on grammars rather than parser-combinators, or allow
;;    the two to be intermixed. This and (3) are essentially the same idea,
;;    seen through different lenses.
;;
;; I think I like solution 3 or 4 best in the long run. The only particular
;; problem they present is "garbage collection": removing parts of the
;; graph/grammar that aren't referenced.
(define derive-memo (make-parameter (hash)))
(define (derive c p)
  (printf "derive ~v\n" p)
  (match p
    [(p/rec name contents)
     ;; formatting the name like this is nice for debugging, but in a real
     ;; implementation it would result in growing space usage over time.
     (define deriv-name (gensym (format "d_~a" name)))
     ;; we map `name' to (parse-null p) in parse-null-memo, because we call
     ;; `parse-null' within `derive' (in the p/apply case), and we want it to
     ;; work even under this p/rec binder. this is an awful terrible no-good
     ;; interface-violating hack, but it works. (*cross fingers*)
     (parameterize ([parse-null-memo
                     (hash-set (parse-null-memo) name (parse-null p))]
                    [derive-memo
                     (hash-set (derive-memo) name (p-var deriv-name))])
       (substitute p name (p/rec deriv-name (derive c contents))))]
    [(p/var name)   (hash-ref (derive-memo) name)]
    [(p/pure _)     p-empty]
    [(p/tok (== c)) (p-eps c)]
    [(p/tok _)      p-empty]
    [(p/union ps)   (p-union (map (curry derive c) ps))]
    [(p/apply f ps)
     ;; This call to parse-null is only guaranteed to work because of the trick
     ;; pulled above with parse-null-memo.
     (define nulls  (map parse-null ps))
     (define derivs (map (curry derive c) ps))
     (p-union
      (for/list ([i (length ps)])
        (define head (take nulls i))
        (define tail (drop ps (+ 1 i)))
        (p-apply f (append (map p-pure head)
                           (list (list-ref derivs i))
                           tail))))]))

;; compact no longer even needs to be memoized! it just uses the p/rec & p/var
;; structure to know when to stop recursing.
;;
;; TODO: if a recursive parser doesn't actually refer to itself, remove the
;; p/rec.
(define (compact p)
  (match p
    [(? is-empty?)      p-empty]
    [(p/rec name contents)
     ;; ugh, this hack again.
     (parameterize ([is-empty-memo
                     (hash-set (is-empty-memo) name (is-empty? p))])
       (p/rec name (compact contents)))]
    [(p/var name)       p]
    [(p/pure _)         p]
    [(p/tok _)          p]
    ;; Our smart constructors do most of the work for us.
    [(p/union ps)       (p-union (map compact ps))]
    [(p/apply f ps)     (p-apply f (map compact ps))]))


;; =============== Running parsers ===============
(define (parse p toks)
  (match toks
    ['() (parse-null p)]
    [(cons tok toks) (parse (derive tok p) toks)]))


;; =============== Test cases ===============
(define-rule self self)
(define-rule infsum infsum infsum)
(define-rule inflist (list inflist inflist))

(define-rule nat 'z (list 's nat))
(define-rule zs (eps '()) (cons 'z zs))
