#lang racket
(require redex)

(require "ziria.rkt")

;;
;; A few simple typing judgment tests
;;
(test-equal
 (judgment-holds
  (types () 1 τ)
  τ)
 (list (term int)))

(test-equal
 (judgment-holds
  (types ((x int)) x τ)
  τ)
 (list (term int)))

(test-equal
 (judgment-holds
  (types () (+ 1 3) τ)
  τ)
 (list (term int)))

(test-equal
 (judgment-holds
  (types () (- 1) τ)
  τ)
 (list (term int)))

(test-equal
 (judgment-holds
  (types ((x (ref int))) x θ)
  θ)
 (list (term (ref int))))

(test-equal
 (judgment-holds
  (types ((x (ref int))) (set x (+ 3 4)) (ST (C unit) int int)))
 #t)

;;
;; Testing the thread reduction relation
;;

(define (test-eval-exp Σ H e1 e2)
  (define (thread-exp-matches t)
    (match t
      [`(thread ,_ ,_ ,e halt tick) (eq? e e2)]
      [_ #f]))
  (test-->>∃
   Zred
   (term (thread ,Σ ,H ,e1 halt tick))
   thread-exp-matches))

(test-eval-exp '() '()
               (term (if (= 10 (+ 9 1)) (+ 1 10) (- 19)))
               11)

(test-eval-exp '((x l)) '((l 3))
               (term (if (= x 3) 1 0))
               1)

(test-eval-exp '() '()
               (term (let x (+ 1 2) (+ x x)))
               6)

(test-eval-exp '() '()
               (term (letfun plus ((x : int) (y : int)) (+ x y) (plus 1 2)))
               3)

(test-eval-exp '() '()
               (term (letfun fact ((x : int)) (if (< x 2) 1 (* x (fact (- x 1)))) (fact 4)))
               24)

;;
;; Testing the machine reduction rule
;;

(define-syntax do
  (syntax-rules (let letref letfun <- >>>)
    [(_ let x e rest ...) (term (let x e ,(do rest ...)))]
    [(_ letref x e rest ...) (term (letref x e ,(do rest ...)))]
    [(_ letfun f args e rest ...) (term (letfun f args e ,(do rest ...)))]
    [(_ e) (term e)]
    [(_ e1 >>> e2) (term (arr ,e1 ,e2))]
    [(_ v <- e rest ...)
     (term (bind v ,(do e) ,(do rest ...)))]
    [(_ e rest ...)
     (term (seq e ,(do rest ...)))]
    [(_ return e)
     (term (return e))]))

;;
;; Convert a Ziria expression and input into an initial machine configuration
;;
(define (exp->mach e in)
  (term (mach ((q_1 (queue ,@in)) (q_2 (queue))) ((proc (thread () () ,e halt tick) q_1 q_2)))))

;;
;; Test that running a Ziria expression with a given intput yields the specified output
;;
(define (test-output e in out)
  (define (mach-output-matches? m)
    (match m
      [`(mach (,_ ... (,_ (queue ,v ...))) ,_) (equal? out v)]
      [_ #f]))
  (test-->>∃
   Zmach
   (exp->mach e in)
   mach-output-matches?))

(define pipe
  (term (repeat ,(do x <- take
                     (emit x)))))

(define (map f)
  (term (repeat ,(do x <- take
                     (emit (,f x))))))

(test-output (do letfun f ((x : int)) (+ x 1)
                 ,(map 'f))
             '(1 2 3 4 5)
             '(2 3 4 5 6))

;;
;; A well-typed term since we can split the heap
;;
(define test
  (do letref x 0
      (term (repeat ,(do z1 <- (deref x)
                         z2 <- take
                         (emit z1)
                         (emit z2)
                         (set x (+ z1 z2)))))
      >>>
      (term (repeat ,(do z <- take
                         (emit z))))))

(test-equal
 (judgment-holds
  (types () ,test (ST T int int)))
 #t)

(test-output test
             '(1 2)
             '(0 1 1 2))

;;
;; Not a well-typed term since we *cannot* split the heap
;;
(define test2
  (do letref x 0
      (term (repeat ,(do z1 <- (deref x)
                         z2 <- take
                         (emit z1)
                         (emit z2)
                         (set x (+ z1 z2)))))
      >>>
      (do z <- take
          (set x z)
          (emit z))))

(test-equal
 (judgment-holds
  (types () ,test2 θ) θ)
 '())

;;(traces Zmach (exp->mach pipe '(1 2)))
 
;(traces Zmach (exp->mach (do letfun f ((x : int)) (+ x 1)
;                             ,(map 'f))
;                         '(1 2)))
