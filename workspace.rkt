#lang plai-typed

(require (typed-in racket/base [findf : (('a -> boolean) (listof 'a) -> 'a)]))

;; Todo
;;; - think about error handling, maybe put it in a few places 
;;;;  - don't really want to go crazy as this is for learning

(define-type ExprC
  [idC (s : symbol)]
  [appC (fun : ExprC) (arg : ExprC)]
  [numC (n : number)]
  [plusC (l : ExprC) (r : ExprC)]
  [multC (l : ExprC) (r : ExprC)]
  [lamC (arg : symbol) (body : ExprC)])

(define-type Value
  [numV (n : number)]
  [clsV (arg : symbol) (body : ExprC) (env : Env)])

(define-type ExprS
  [numS (n : number)]
  [plusS (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [multS (l : ExprS) (r : ExprS)]
  [uminusS (e : ExprS)]
  [idS (id : symbol)]
  [appS (fun : ExprS) (expr : ExprS)]
  [lamS (arg : symbol) (expr : ExprS)])

(define-type Binding
  [bind (name : symbol) (val : Value)])

(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)

(define (lookup [for : symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "name not found")]
    [else (cond
            [(symbol=? for (bind-name (first env)))
             (bind-val (first env))]
            [else (lookup for (rest env))])]))

(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))]
    [(s-exp-list? s) 
       (let ([s1 (s-exp->list s)])
         (if (s-exp-symbol? (first s1)) ;; (if (application? s1) <handle-builtins> <handle-application>)
             (case (s-exp->symbol (first s1))
               ['+ (plusS (parse (second s1)) (parse (third s1)))]
               ['* (multS (parse (second s1)) (parse (third s1)))]
               ['- (if (= (length s1) 2) (uminusS (parse (second s1)))
                       (bminusS (parse (second s1)) (parse (third s1))))]
               ['λ (lamS (s-exp->symbol (second s1))
                         (parse (third s1)))]
               ;; TODO seems weird to need the same appS expression below.. how to refactor?
               [else (appS (parse (first s1))
                           (parse (second s1)))])
             (appS (parse (first s1))
                   (parse (second s1)))))]))

;; Parsing Tests

;;; Numbers
(test (parse '2)
      (numS 2))

;;; Ids
(test (parse (symbol->s-exp 'x))
      (idS 'x))

;;; Math
(test (parse '(+ (* 1 2) (+ 2 3)))
      (plusS (multS (numS 1) (numS 2)) (plusS (numS 2) (numS 3))))

(test (parse '(+ 1 x))
      (plusS (numS 1) (idS 'x)))

;;; Lambda
(test (parse '(λ x (+ 1 x)))
      (lamS 'x (plusS (numS 1) (idS 'x))))

(test (parse '((λ x (+ 1 x))
              5))
      (appS (lamS 'x (plusS (numS 1) (idS 'x)))
            (numS 5)))

;;; Let
(test (parse '(let (x 2)
                x))
      (letS (idS 'x) (numS 2) (idS 'x)))


(define (lift-op [op : (number number -> number)]) : (Value Value -> Value)
  (λ ([l : Value] [r : Value]) : Value
    (cond
      [(and (numV? l) (numV? r))
       (numV (op (numV-n l) (numV-n r)))]
      [else
       (error 'num+ "non-number argument")])))

(define num+ (lift-op +))
(define num* (lift-op *))


(define (desugar [as : ExprS]) : ExprC
  (type-case ExprS as
    [numS (n) (numC n)]
    [plusS (l r) (plusC (desugar l)
                        (desugar r))]
    [multS (l r) (multC (desugar l) 
                        (desugar r))]
    [bminusS (l r) (plusC (desugar l) 
                          (multC (numC -1) 
                                 (desugar r)))]
    [uminusS (e) (multC (numC -1)
                        (desugar e))]
    [idS (id) (idC id)]
    [appS (f a) (appC (desugar f) (desugar a))]
    [lamS (a b) (lamC a (desugar b))]))

(define (interp [a : ExprC] [env : Env] ) : Value
  (type-case ExprC a
    [numC (n) (numV n)]
    [plusC (l r) (num+ (interp l env) (interp r env))]
    [multC (l r) (num* (interp l env) (interp r env))]
    [idC (n) (lookup n env)]
    [appC (f a) (local ([define fV (interp f env)])
                  ;; should check here that fV is actually a function
                  (if (not (clsV? fV))
                      (error 'interp (string-append (to-string fV) 
                                                    " is not a function value"))
                      (interp (clsV-body fV)
                              (extend-env (bind (clsV-arg fV)
                                                (interp a env))
                                          (clsV-env fV)))))]
    [lamC (a b) (clsV a b env)]))

;; TODO add conditionals
;(define-type CondE
;  [condE (test-exp : ExprS) (
; (test ...)
       

;; interpreter test cases
(define (evaluate* [form : s-expression] [env : Env]) : Value
  (interp (desugar (parse form))
          env))

(define (evaluate [form : s-expression]) : Value
  (evaluate* form mt-env))


;; Tests

;;; Basic Arithmetic (incl. parsing)
(test (evaluate '2) (numV 2))
(test (evaluate '(- 1 2)) (numV -1))
(test (evaluate '(+ 1 2)) (numV 3))
(test (evaluate '(- (+ 1 2))) (numV -3))
(test (evaluate '(* 2 3)) (numV 6))
(test (evaluate '(* (+ (* 2 3) (+ 1 2)) 2)) (numV 18))


;;; Lambda expressions (core only, no sugar, no parse)
;;;; raw interp
(test (interp (lamC 'x (plusC
                        (idC 'x)
                        (numC 1)))
              mt-env)
      (clsV 'x (plusC (idC 'x) (numC 1)) mt-env))

(test (interp (appC (lamC 'x (plusC
                        (idC 'x)
                        (numC 1)))
                    (numC 5))
              mt-env)
      (numV 6))

;;;; the whole thing
(test (evaluate '(λ x (+ 1 x))) (clsV 'x (plusC (numC 1) (idC 'x)) mt-env)) 
(test (evaluate '((λ x (+ 1 x)) 5)) (numV 6))
(test (evaluate* '(f 5) (extend-env (bind 'f (evaluate '(λ x (+ 1 x))))
                                    mt-env))
      (numV 6))

;; test substituion. 
(test (evaluate '(((λ f 
                     (λ x 
                       (f 10)))
                   (λ x 
                     (+ x 1))) 
                  5))
      (numV 11))

;; test error message on non-function in application position
(test/exn (evaluate '(2 3)) "not a function value")

;; the book suggests the following should error:
;;; (evaluate '(λ x1 ((λ y1 (+ x y1)) 10)))
;; I agree. Did my interpreter diverge too far from the book?
;; It does, of course, fail if actually applied to an argument.
;; This succeeds because I don't interpret the body of a lambda
;; until it is applied to something.  Does the book do something
;; different?

;(define (def-λ [arg : symbol] [e : s-expression]) : ExprC
;  (lamC arg (desugar (parse e))))
;
;(define f (def-λ 'x '(* x 2)))
;(define z (def-λ 'x '(+ x 3)))
;(define g (def-λ 'x '(+ x y)))
;(define h (def-λ 'y '(g 2)))
;
;(define env-with-fns (extend-env 
;                      mt-env)
;
;(test (evaluate* '(f 2) (list f)) 4)
;(test (evaluate* '(f (f 2)) (list f z)) 8)
;(test (evaluate* '(f (z 2)) (list f z)) 10)
;(test (evaluate* '(f (z 2)) (list z f)) 10)
;(test (evaluate* '(f (z (+ (f 3) (z (* (f 3) 2)))))
;                 
;                              48)
;(test/exn (evaluate* '(h 3) (list z g f h)) "name not found")
