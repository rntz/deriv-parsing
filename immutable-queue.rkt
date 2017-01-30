#lang racket

;; really I'd like to do data hiding on queue - so you can't construct or
;; pattern match on it outside this module - but I don't know how to do that. I
;; guess I could use the object-oriented machinery, but bleh.
(provide
 (struct-out queue)
 list->queue empty-queue queue-empty? queue-append enqueue dequeue queue->list)

;; we read by popping from front and write by pushing on back.
(struct queue (front back)
  #:transparent)

(define (list->queue l) (queue l '()))

(define (queue->list q)
  (match-define (queue f b) q)
  (append f (reverse b)))

(define empty-queue (list->queue '()))

(define (queue-empty? q)
  (match q [(queue '() '()) #t] [_ #f]))

(define (queue-append q elems)
  (match-define (queue f b) q)
  (queue f (append (reverse elems) b)))

(define (enqueue q x)
  (match-define (queue f b) q)
  (queue f (cons x b)))

(define (dequeue q)
  (match q
    [(queue '() '())        (error "dequeueing from empty queue")]
    [(queue '() b)          (dequeue (queue (reverse b) '()))]
    [(queue (cons x f) b)   (values (queue f b) x)]))
