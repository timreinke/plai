#lang plai-typed

(require (typed-in racket/base [findf : (('a -> boolean) (listof 'a) -> 'a)]))

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
         (case (s-exp->symbol (first s1))
           ['+ (plusS (parse (second s1)) (parse (third s1)))]
           ['* (multS (parse (second s1)) (parse (third s1)))]
           ['- (if (= (length s1) 2) (uminusS (parse (second s1)))
                   (bminusS (parse (second s1)) (parse (third s1))))]
           ;; otherwise, just assume it's function application
           ;; if it's not, it's not a valid program anyway (though
           ;; a friendly parser may catch the error here e.g. a number
           ;; in the function application position).  
           ;; at this point, only functions of one argument are
           ;; supported
           [else (appS (parse (first s1))
                       (parse (second s1)))]))]))


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
    [appS (f a) (appC (desugar f) (desugar a))]
    [lamS (a b) (lamC a (desugar b))]))

(define (interp [a : ExprC] [env : Env] ) : Value
  (type-case ExprC a
    [numC (n) (numV n)]
    [plusC (l r) (num+ (interp l env) (interp r env))]
    [multC (l r) (num* (interp l env) (interp r env))]
    [idC (n) (lookup n env)]
    [appC (f a) (local ([define fV (interp f env)])
                  (interp (clsV-body fV)
                          (extend-env (bind (clsV-arg fV)
                                            (interp a env))
                                      (clsV-env fV))))]
    [lamC (a b) (clsV a b env)]))

;; TODO add conditionals
;(define-type CondE
;  [condE (test-exp : ExprS) (
; (test ...)
       

;; interpreter test cases
(define (evaluate* [form : s-expression] [env : Env]) : number
  (numV-n (interp (desugar (parse form))
          env)))

(define (evaluate [form : s-expression]) : number
  (evaluate* form mt-env))


;; Tests

;;; Basic Arithmetic (incl. parsing)
(test (evaluate '2) 2)
(test (evaluate '(- 1 2)) -1)
(test (evaluate '(+ 1 2)) 3)
(test (evaluate '(- (+ 1 2))) -3)
(test (evaluate '(* 2 3)) 6)
(test (evaluate '(* (+ (* 2 3) (+ 1 2)) 2)) 18)


;;; Lambda expressions (core only, no sugar, no parse)
(test (interp (lamC 'x (plusC
                        (idC 'x)
                        (numC 1)))
              mt-env)
      (clsV 'x (plusC (idC 'x) (numC 1)) mt-env))

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
