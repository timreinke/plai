#lang plai-typed

;; TODO
;; - warn on incorrect number of arguments to all expressions e.g. now (+ 1 2 3) => 3
;; - add conditionals
;; - more tests

(require 
 (typed-in racket/base [findf : (('a -> boolean) (listof 'a) -> 'a)])
 (rename-in 
  (typed-in racket/base [foldl : (('a 'b 'c -> 'c) 'c (listof 'a) (listof 'b) -> 'c)])
  [foldl foldl2]))
                                                              

(define-type ExprC
  [idC (s : symbol)]
  [numC (n : number)]
  [plusC (l : ExprC) (r : ExprC)]
  [multC (l : ExprC) (r : ExprC)]
  [appC (fun : ExprC) (args : (listof ExprC))]
  [lamC (args : (listof symbol)) (body : ExprC)])

(define-type Value
  [numV (n : number)]
  [clsV (names : (listof symbol)) (body : ExprC) (env : Env)])

(define-type BindingS
  [bindingS (id : symbol) (expr : ExprS)])

(define-type ExprS
  [numS (n : number)]
  [plusS (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [multS (l : ExprS) (r : ExprS)]
  [uminusS (e : ExprS)]
  [idS (id : symbol)]
  [letS (bindings : (listof BindingS)) (body : ExprS)]
  [appS (fun : ExprS) (exprs : (listof ExprS))]
  [lamS (args : (listof symbol)) (expr : ExprS)])

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

(define (parse-binding-pairs [bindings : (listof s-expression)]) : (listof BindingS)
  (map
   (λ ([binding-form : s-expression]) : BindingS
     (if (s-exp-list? binding-form)
         (let ([binding-form* (s-exp->list binding-form)])
           (bindingS (s-exp->symbol (first binding-form*))
                     (parse (second binding-form*))))
         (error 'let "invalid binding form. expected symbol, expr pair")))
   bindings))

(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))]
    [(s-exp-list? s)
       (let ([s1 (s-exp->list s)])
         (cond 
           [(s-exp-list? (first s1)) (appS (parse (first s1)) (map parse (rest s1)))] 
           [else  
            (case (s-exp->symbol (first s1))
              ['+ (plusS (parse (second s1)) (parse (third s1)))]
              ['* (multS (parse (second s1)) (parse (third s1)))]
              ['- (if (= (length s1) 2) (uminusS (parse (second s1)))
                      (bminusS (parse (second s1)) (parse (third s1))))]
              ['let (if (s-exp-list? (second s1))
                        (let ([binding-pairs (s-exp->list (second s1))])
                          (letS (parse-binding-pairs binding-pairs)
                                (parse (third s1))))
                        (error 'let "invalid binding syntax. expected list"))]
              ['λ (lamS (map s-exp->symbol (s-exp->list (second s1))) (parse (third s1)))]
              [else (appS (parse (first s1))
                          (map parse (rest s1)))])]))]))


(test (parse '(+ (* 1 2) (+ 2 3)))
      (plusS (multS (numS 1) (numS 2)) (plusS (numS 2) (numS 3))))


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
    [appS (f a) (appC (desugar f) (map desugar a))]
    [lamS (a b) (lamC a (desugar b))]
    [letS (bindings body) 
          (let ([names (map bindingS-id bindings)]
                [exprs (map bindingS-expr bindings)])
            (desugar (appS (lamS names body)
                           exprs)))]))

(define (interp [a : ExprC] [env : Env] ) : Value
  (type-case ExprC a
    [numC (n) (numV n)]
    [plusC (l r) (num+ (interp l env) (interp r env))]
    [multC (l r) (num* (interp l env) (interp r env))]
    [idC (n) (lookup n env)]
    [appC (f args) (local ([define fV (interp f env)])
                     (interp 
                      (clsV-body fV)
                      (foldl2 (λ ([name : symbol] [expr : ExprC] [env : Env]) : Env
                                (extend-env (bind name
                                                  (interp expr env))
                                            env))
                              (clsV-env fV)
                              (clsV-names fV)
                              args)))]
    [lamC (args b) (clsV args b env)]))

;; TODO add conditionals
;(define-type CondE
;  [condE (test-exp : ExprS) (
; (test ...)
       

;; interpreter test cases
(define (evaluate* [form : s-expression] [env : Env]) : Value
  (interp (desugar (parse form))
          env))

(define (evaluate [form : s-expression]) : number
  (numV-n (evaluate* form mt-env)))


(test (evaluate '2) 2)
(test (evaluate '(- 1 2)) -1)
(test (evaluate '(+ 1 2)) 3)
(test (evaluate '(- (+ 1 2))) -3)
(test (evaluate '(* 2 3)) 6)
(test (evaluate '(* (+ (* 2 3) (+ 1 2)) 2)) 18)
(test (evaluate '(+ 10 ((λ (x y) (- x y)) 10 20))) 0) 
(test (evaluate* '(+ 10 (f 10 20)) (extend-env (bind 'f (evaluate* '(λ (x y) (- x y)) mt-env))
                                              mt-env))
      (numV 0))
(test (evaluate '(let ((a 5)) a)) 5)
(test (evaluate '(let ((a 5)
                       (b (λ (x) (+ x x))))
                   (b a)))
      10)

;(define f (def-fd 'f 'x '(* x 2)))
;(define z (def-fd 'z 'x '(+ x 3)))
;(define g (def-fd 'g 'x '(+ x y)))
;(define h (def-fd 'h 'y '(g 2)))
;(test (evaluate* '(f 2) (list f)) 4)
;(test (evaluate* '(f (f 2)) (list f z)) 8)
;(test (evaluate* '(f (z 2)) (list f z)) 10)
;(test (evaluate* '(f (z 2)) (list z f)) 10)
;(test (evaluate* '(f (z (+ (f 3) (z (* (f 3) 2))))) (list z f)) 48)
;(test/exn (evaluate* '(h 3) (list z g f h)) "name not found")
